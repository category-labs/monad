// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use std::{
    collections::{btree_map::Entry as BTreeMapEntry, BTreeMap},
    path::PathBuf,
    sync::Arc,
    time::{Duration, Instant},
};

use alloy_primitives::{Address, U256};
use chrono::DateTime;
use clap::Parser;
use itertools::Itertools;
use monad_event_ring::{DecodedEventRing, EventNextResult};
use monad_exec_events::{
    ffi::{monad_exec_block_end, monad_exec_block_start, monad_exec_block_tag},
    BlockBuilderError, BlockBuilderResult, BlockCommitState, CommitStateBlockBuilder,
    CommitStateBlockUpdate, ExecEventRing, ExecutedBlock, ExecutedBlockBuilder, ExecutedTxn,
};
use ratatui::{
    crossterm::event::{Event, KeyCode, KeyModifiers},
    layout::{Constraint, Layout, Margin, Rect},
    style::{Color, Modifier, Style, Stylize},
    text::{Line, Span, Text},
    widgets::{
        Block, Cell, HighlightSpacing, Padding, Paragraph, Row, Scrollbar, ScrollbarOrientation,
        ScrollbarState, Table, TableState, Tabs, Widget,
    },
    DefaultTerminal, Frame,
};
use strum::IntoEnumIterator;

#[derive(Debug, Parser)]
#[command(name = "monad-exec-events-explorer", about, long_about = None)]
pub struct Cli {
    #[arg(long)]
    event_ring_path: PathBuf,
}

const PADDING_COLUMN: u16 = 2;
const MAX_ROUNDS_LEN: usize = 1024;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let terminal = ratatui::init();
    let app_result = App::new(cli).run(terminal);
    ratatui::restore();
    app_result
}

struct App {
    event_ring_path: PathBuf,

    rounds: BTreeMap<u64, (Option<BlockCommitState>, Arc<ExecutedBlock>)>,

    view: View,

    overview_table_state: TableState,
    overview_scroll_state: ScrollbarState,
    overview_frozen_buffer: Option<Vec<BlockBuilderResult<CommitStateBlockUpdate>>>,

    block_tab: BlockTab,
    block_current: Option<Arc<ExecutedBlock>>,

    block_header_table_state: TableState,
    block_execution_result_table_state: TableState,
    block_txns_table_state: TableState,
}

#[derive(Copy, Clone, strum::Display, strum::EnumIter, strum::FromRepr)]
enum View {
    Overview,
    Block,
}

#[derive(Copy, Clone, strum::Display, strum::EnumIter, strum::FromRepr)]
enum BlockTab {
    Header,
    ExecutionResult,
    Txs,
}

impl App {
    fn new(cli: Cli) -> Self {
        let Cli { event_ring_path } = cli;

        Self {
            event_ring_path,

            rounds: BTreeMap::default(),

            view: View::Overview,

            overview_table_state: TableState::default(),
            overview_scroll_state: ScrollbarState::default().viewport_content_length(3),
            overview_frozen_buffer: None,

            block_tab: BlockTab::Header,
            block_current: None,

            block_header_table_state: TableState::default().with_selected(0),
            block_execution_result_table_state: TableState::default().with_selected(0),
            block_txns_table_state: TableState::default().with_selected(0),
        }
    }

    pub fn next_row(&mut self) {
        self.next_n_rows(1);
    }

    pub fn next_n_rows(&mut self, amount: u16) {
        match self.view {
            View::Overview => {
                self.overview_table_state.scroll_down_by(amount);

                if let Some(selected) = self.overview_table_state.selected() {
                    self.overview_scroll_state = self.overview_scroll_state.position(selected);
                }
            }
            View::Block => match self.block_tab {
                BlockTab::Header => {
                    self.block_header_table_state.scroll_down_by(amount);
                }
                BlockTab::ExecutionResult => {
                    self.block_execution_result_table_state
                        .scroll_down_by(amount);
                }
                BlockTab::Txs => {
                    self.block_txns_table_state.scroll_down_by(amount);
                }
            },
        }
    }

    pub fn previous_row(&mut self) {
        self.previous_n_rows(1);
    }

    pub fn previous_n_rows(&mut self, amount: u16) {
        match self.view {
            View::Overview => {
                self.overview_table_state.scroll_up_by(amount);

                if let Some(selected) = self.overview_table_state.selected() {
                    self.overview_scroll_state = self.overview_scroll_state.position(selected);
                }
            }
            View::Block => match self.block_tab {
                BlockTab::Header => {
                    self.block_header_table_state.scroll_up_by(amount);
                }
                BlockTab::ExecutionResult => {
                    self.block_execution_result_table_state.scroll_up_by(amount);
                }
                BlockTab::Txs => {
                    self.block_txns_table_state.scroll_up_by(amount);
                }
            },
        }
    }

    pub fn first_row(&mut self) {
        match self.view {
            View::Overview => {
                self.overview_table_state.select_first();

                if let Some(selected) = self.overview_table_state.selected() {
                    self.overview_scroll_state = self.overview_scroll_state.position(selected);
                }
            }
            View::Block => match self.block_tab {
                BlockTab::Header => {
                    self.block_header_table_state.select_first();
                }
                BlockTab::ExecutionResult => {
                    self.block_execution_result_table_state.select_first();
                }
                BlockTab::Txs => {
                    self.block_txns_table_state.select_first();
                }
            },
        }
    }

    pub fn last_row(&mut self) {
        match self.view {
            View::Overview => {
                self.overview_table_state.select_last();

                if let Some(selected) = self.overview_table_state.selected() {
                    self.overview_scroll_state = self.overview_scroll_state.position(selected);
                }
            }
            View::Block => match self.block_tab {
                BlockTab::Header => {
                    self.block_header_table_state.select_last();
                }
                BlockTab::ExecutionResult => {
                    self.block_execution_result_table_state.select_last();
                }
                BlockTab::Txs => {
                    self.block_txns_table_state.select_last();
                }
            },
        }
    }

    pub fn move_forward(&mut self) {
        match self.view {
            View::Overview => {
                if let Some(selected) = self.overview_table_state.selected() {
                    let block = self.rounds.iter().nth(selected).unwrap().1 .1.clone();

                    self.view = View::Block;
                    self.block_current = Some(block);
                }
            }
            View::Block => match self.block_tab {
                BlockTab::Header => {
                    self.block_tab = BlockTab::ExecutionResult;
                }
                BlockTab::ExecutionResult => {
                    self.block_tab = BlockTab::Txs;
                }
                BlockTab::Txs => {}
            },
        }
    }

    pub fn move_back(&mut self) {
        match self.view {
            View::Overview => {}
            View::Block => match self.block_tab {
                BlockTab::Header => {
                    self.view = View::Overview;
                    self.block_current = None;
                }
                BlockTab::ExecutionResult => {
                    self.block_tab = BlockTab::Header;
                }
                BlockTab::Txs => {
                    self.block_tab = BlockTab::ExecutionResult;
                }
            },
        }
    }

    fn run(mut self, mut terminal: DefaultTerminal) -> Result<(), Box<dyn std::error::Error>> {
        let event_ring = ExecEventRing::new_from_path(&self.event_ring_path).unwrap();

        let mut event_reader = event_ring.create_reader();

        let mut block_builder = CommitStateBlockBuilder::new(ExecutedBlockBuilder::new(false));

        let tick_rate = Duration::from_millis(100);
        let mut last_tick = Instant::now();

        loop {
            loop {
                let event_descriptor = match event_reader.next_descriptor() {
                    EventNextResult::Gap => panic!("event ring gapped"),
                    EventNextResult::NotReady => break,
                    EventNextResult::Ready(event) => event,
                };

                let Some(result) = block_builder.process_event_descriptor(&event_descriptor) else {
                    continue;
                };

                if let Some(frozen_buffer) = self.overview_frozen_buffer.as_mut() {
                    frozen_buffer.push(result);
                } else {
                    self.process_state_result(result);
                }
            }

            while self.rounds.len() > MAX_ROUNDS_LEN {
                self.rounds.pop_first();
                match &self.view {
                    View::Overview => {
                        self.previous_row();
                    }
                    View::Block => {}
                }
            }

            terminal.draw(|frame| self.draw(frame))?;

            let timeout = tick_rate.saturating_sub(last_tick.elapsed());
            if ratatui::crossterm::event::poll(timeout)? {
                if let Event::Key(key) = ratatui::crossterm::event::read()? {
                    match key.code {
                        KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                        KeyCode::Char('c') if key.modifiers == KeyModifiers::CONTROL => {
                            return Ok(())
                        }
                        KeyCode::Char('j') | KeyCode::Down => {
                            self.next_row();
                        }
                        KeyCode::Char('k') | KeyCode::Up => {
                            self.previous_row();
                        }
                        KeyCode::Home => {
                            self.first_row();
                        }
                        KeyCode::Char('G') | KeyCode::End => {
                            self.last_row();
                        }
                        KeyCode::Char('l') | KeyCode::Right => {
                            self.move_forward();
                        }
                        KeyCode::Char('h') | KeyCode::Left => {
                            self.move_back();
                        }
                        _ => match self.view {
                            View::Overview => match key.code {
                                KeyCode::Enter => {
                                    self.move_forward();
                                }
                                KeyCode::Char(' ') => {
                                    if let Some(frozen_buffer) = self.overview_frozen_buffer.take()
                                    {
                                        for result in frozen_buffer {
                                            self.process_state_result(result);
                                        }
                                    } else {
                                        self.overview_frozen_buffer = Some(Vec::default());
                                    }
                                }
                                _ => {}
                            },
                            View::Block => {}
                        },
                    }
                }
            }

            if last_tick.elapsed() >= tick_rate {
                last_tick = Instant::now();
            }
        }
    }

    fn process_state_result(&mut self, result: BlockBuilderResult<CommitStateBlockUpdate>) {
        match result {
            Err(BlockBuilderError::Rejected) => unreachable!(),
            Err(BlockBuilderError::ImplicitDrop { .. }) => unreachable!(),
            Err(BlockBuilderError::PayloadExpired) => {
                panic!("event ring payload expired")
            }
            Ok(CommitStateBlockUpdate {
                block,
                state,
                abandoned,
            }) => {
                let rounds_len = self.rounds.len();

                match self.rounds.entry(block.start.round) {
                    BTreeMapEntry::Vacant(v) => {
                        let was_selecting_last =
                            self.overview_table_state
                                .selected()
                                .is_some_and(|selected_row| {
                                    selected_row == rounds_len.saturating_sub(1)
                                });

                        v.insert((Some(state), block));

                        if was_selecting_last && matches!(self.view, View::Overview) {
                            self.last_row();
                        }
                    }
                    BTreeMapEntry::Occupied(mut o) => {
                        o.get_mut().0 = Some(state);
                    }
                }

                if rounds_len == 0 && self.rounds.len() == 1 {
                    self.first_row();
                }

                for abandoned in abandoned {
                    self.rounds.get_mut(&abandoned.start.round).unwrap().0 = None;
                }

                self.overview_scroll_state =
                    self.overview_scroll_state.content_length(self.rounds.len());
            }
        }
    }

    fn draw(&mut self, frame: &mut Frame) {
        let areas = Layout::vertical([Constraint::Length(3), Constraint::Fill(u16::MAX)])
            .split(frame.area());

        let titles = View::iter().map(|tab| Line::from(format!("\n{tab}\n")));

        let tabs_block = Block::new().bg(Color::Blue).padding(Padding::uniform(1));

        Tabs::new(titles)
            .fg(Color::Gray)
            .select(self.view as usize)
            .highlight_style(Style::default().fg(Color::White).bold())
            .padding("  ", "  ")
            .divider("  ")
            .block(tabs_block)
            .render(areas[0], frame.buffer_mut());

        let logo = Paragraph::new("Category Labs").centered().block(
            Block::new()
                .fg(Color::Black)
                .bg(Color::Rgb(255, 85, 0))
                .padding(Padding::uniform(1)),
        );

        frame.render_widget(
            logo,
            Rect {
                x: areas[0].x + areas[1].width - 17,
                y: areas[0].y,
                width: 17,
                height: areas[0].height,
            },
        );

        match &self.view {
            View::Overview => {
                self.render_overview_table(frame, areas[1]);
                self.render_overview_scrollbar(frame, areas[1]);
            }
            View::Block => {
                self.render_block(frame, areas[1]);
            }
        }
    }

    fn render_overview_table(&mut self, frame: &mut Frame, area: Rect) {
        let header_style =
            Style::default()
                .fg(Color::White)
                .bg(if self.overview_frozen_buffer.is_some() {
                    Color::Red
                } else {
                    Color::Green
                });
        let selected_row_style = Style::default().add_modifier(Modifier::REVERSED);

        let header_strs = [
            "Round Number",
            "Commit State",
            "Proposal ID",
            "Block Number",
            "Block Time",
            "Block Txns",
        ];

        let header = header_strs
            .into_iter()
            .map(|header_str| format!("\n{header_str}\n"))
            .map(|header| Cell::from(Text::from(header).centered()))
            .collect::<Row>()
            .style(header_style)
            .height(3);

        let rows = self.rounds.iter().map(|(round, (state, block))| {
            [
                Text::from(round.to_string()),
                Text::from(match state {
                    Some(BlockCommitState::Proposed) => "Proposed".light_red(),
                    Some(BlockCommitState::Voted) => "Voted".light_yellow(),
                    Some(BlockCommitState::Finalized) => "Finalized".light_blue(),
                    Some(BlockCommitState::Verified) => "Verified".light_green(),
                    None => "Abandoned".dark_gray(),
                }),
                Text::from(hex::encode(block.start.block_tag.id.bytes)),
                Text::from(
                    Span::raw(block.start.block_tag.block_number.to_string()).style(
                        if state.is_none() {
                            Style::default().crossed_out()
                        } else {
                            Style::default()
                        },
                    ),
                ),
                Text::from(
                    DateTime::from_timestamp(
                        block.start.eth_block_input.timestamp.try_into().unwrap(),
                        0,
                    )
                    .unwrap()
                    .to_rfc3339(),
                ),
                Text::from(block.start.eth_block_input.txn_count.to_string()),
            ]
            .into_iter()
            .map(|mut text| {
                if state.is_none() {
                    for line in text.lines.iter_mut() {
                        line.style.fg = Some(Color::DarkGray);
                    }
                }

                text.lines.insert(0, Line::default());
                text.lines.push(Line::default());

                text.centered()
            })
            .map(Cell::from)
            .collect::<Row>()
            .height(3)
        });

        let bar = " █ ";
        let t = Table::new(
            rows,
            [
                Constraint::Min(
                    TryInto::<u16>::try_into(header_strs[0].len()).unwrap() + PADDING_COLUMN,
                ),
                Constraint::Min(
                    TryInto::<u16>::try_into(header_strs[1].len()).unwrap() + PADDING_COLUMN,
                ),
                Constraint::Length(64 + PADDING_COLUMN),
                Constraint::Min(
                    TryInto::<u16>::try_into(header_strs[3].len()).unwrap() + PADDING_COLUMN,
                ),
                Constraint::Length(25 + PADDING_COLUMN),
                Constraint::Min(
                    TryInto::<u16>::try_into(header_strs[4].len()).unwrap() + PADDING_COLUMN,
                ),
                Constraint::Fill(u16::MAX),
            ],
        )
        .header(header)
        .row_highlight_style(selected_row_style)
        .highlight_symbol(Text::from(vec!["".into(), bar.into(), "".into()]))
        .bg(Color::Reset)
        .highlight_spacing(HighlightSpacing::Always);

        frame.render_stateful_widget(t, area, &mut self.overview_table_state);
    }

    fn render_overview_scrollbar(&mut self, frame: &mut Frame, mut scrollbar_area: Rect) {
        scrollbar_area.y += 3;
        scrollbar_area.height -= 3;

        frame.render_stateful_widget(
            Scrollbar::default()
                .orientation(ScrollbarOrientation::VerticalRight)
                .begin_symbol(None)
                .end_symbol(None),
            scrollbar_area.inner(Margin {
                vertical: 1,
                horizontal: 1,
            }),
            &mut self.overview_scroll_state,
        );
    }

    fn render_block(&mut self, frame: &mut Frame<'_>, area: Rect) {
        let ExecutedBlock { start, end, txns } = self.block_current.as_ref().unwrap().as_ref();

        let areas =
            Layout::vertical([Constraint::Length(3), Constraint::Fill(u16::MAX)]).split(area);

        let titles = BlockTab::iter().map(|tab| Line::from(format!("\n{tab}\n")));

        let tabs_block = Block::new().bg(Color::Cyan).padding(Padding::uniform(1));

        Tabs::new(titles)
            .fg(Color::Gray)
            .select(self.block_tab as usize)
            .highlight_style(Style::default().fg(Color::White).bold())
            .padding("  ", "  ")
            .divider("  ")
            .block(tabs_block)
            .render(areas[0], frame.buffer_mut());

        match self.block_tab {
            BlockTab::Header => {
                Self::render_block_header(
                    frame,
                    areas[1],
                    &mut self.block_header_table_state,
                    start,
                );
            }
            BlockTab::ExecutionResult => {
                Self::render_block_execution_result(
                    frame,
                    areas[1],
                    &mut self.block_execution_result_table_state,
                    end,
                );
            }
            BlockTab::Txs => {
                Self::render_block_txs(frame, areas[1], &mut self.block_txns_table_state, txns);
            }
        }
    }

    fn render_block_header(
        frame: &mut Frame<'_>,
        area: Rect,
        table_state: &mut TableState,
        start: &monad_exec_block_start,
    ) {
        let monad_exec_block_start {
            block_tag: monad_exec_block_tag { id, block_number },
            round,
            epoch,
            __bindgen_padding_0: _,
            proposal_epoch_nanos: _,
            chain_id,
            author: _,
            parent_eth_hash,
            eth_block_input,
            monad_block_input: _,
        } = start;

        let rows: Vec<(&'static str, String, Box<[u8]>)> = vec![
            ("block_tag.id", hex::encode(id.bytes), Box::new(id.bytes)),
            (
                "block_tag.block_number",
                block_number.to_string(),
                Box::new(block_number.to_be_bytes()),
            ),
            ("round", round.to_string(), Box::new(round.to_be_bytes())),
            (
                "epoch",
                start.epoch.to_string(),
                Box::new(epoch.to_be_bytes()),
            ),
            (
                "parent_eth_hash",
                hex::encode(parent_eth_hash.bytes),
                Box::new(parent_eth_hash.bytes),
            ),
            (
                "chain_id",
                U256::from_limbs(chain_id.limbs).to_string(),
                Box::new(unsafe { std::mem::transmute::<[u64; 4], [u8; 32]>(chain_id.limbs) }),
            ),
            (
                "exec_input.base_fee_per_gas",
                U256::from_limbs(eth_block_input.base_fee_per_gas.limbs).to_string(),
                Box::new(unsafe {
                    std::mem::transmute::<[u64; 4], [u8; 32]>(
                        eth_block_input.base_fee_per_gas.limbs,
                    )
                }),
            ),
            (
                "exec_input.beneficiary",
                Address::from(eth_block_input.beneficiary.bytes).to_string(),
                Box::new(eth_block_input.beneficiary.bytes),
            ),
            // TODO(andr-dev): Add remaining exec_input fields
        ];

        Self::render_block_table(frame, area, table_state, rows);
    }

    fn render_block_execution_result(
        frame: &mut Frame<'_>,
        area: Rect,
        table_state: &mut TableState,
        block_result: &monad_exec_block_end,
    ) {
        let monad_exec_block_end {
            eth_block_hash,
            exec_output,
        } = block_result;

        let rows: Vec<(&'static str, String, Box<[u8]>)> = vec![
            (
                "eth_block_hash",
                hex::encode(eth_block_hash.bytes),
                Box::new(eth_block_hash.bytes),
            ),
            (
                "exec_output.gas_used",
                exec_output.gas_used.to_string(),
                Box::new(exec_output.gas_used.to_be_bytes()),
            ),
            (
                "exec_output.logs_bloom",
                hex::encode(exec_output.logs_bloom.bytes),
                Box::new(exec_output.logs_bloom.bytes),
            ),
            (
                "exec_output.receipts_root",
                hex::encode(exec_output.receipts_root.bytes),
                Box::new(exec_output.receipts_root.bytes),
            ),
            (
                "exec_output.state_root",
                hex::encode(exec_output.state_root.bytes),
                Box::new(exec_output.state_root.bytes),
            ),
        ];

        Self::render_block_table(frame, area, table_state, rows);
    }

    fn render_block_table<S>(
        frame: &mut Frame<'_>,
        area: Rect,
        table_state: &mut TableState,
        rows: Vec<(S, String, Box<[u8]>)>,
    ) where
        S: ToString,
    {
        let header = ["Field", "Value", "Hex Dump"]
            .into_iter()
            .map(|header| format!("\n{header}\n"))
            .map(Cell::from)
            .collect::<Row>()
            .height(3);

        let rows = rows.into_iter().map(|(field, value, hex)| {
            [
                field.to_string(),
                value,
                hex.into_vec()
                    .into_iter()
                    .map(|byte| format!("{byte:02x}"))
                    .join(" "),
            ]
            .into_iter()
            .map(|content| Cell::from(Text::from(format!("\n{content}\n"))))
            .collect::<Row>()
            .height(3)
        });

        let bar = " █ ";
        let t = Table::new(
            rows,
            [
                Constraint::Length(32 + 1),
                Constraint::Length(64 + 1),
                Constraint::Fill(u16::MAX),
            ],
        )
        .header(header)
        .row_highlight_style(Style::default().add_modifier(Modifier::REVERSED))
        .highlight_symbol(Text::from(vec!["".into(), bar.into(), "".into()]))
        .highlight_spacing(HighlightSpacing::Always);

        frame.render_stateful_widget(t, area, table_state);
    }

    fn render_block_txs(
        frame: &mut Frame<'_>,
        area: Rect,
        table_state: &mut TableState,
        txns: &[ExecutedTxn],
    ) {
        let rows = txns
            .iter()
            .enumerate()
            .map(|(idx, txn)| {
                [
                    Cell::from(Text::from(format!("\n{idx}\n")).right_aligned()),
                    Cell::from(format!("\n{}\n", hex::encode(txn.hash.bytes))),
                ]
                .into_iter()
                .collect::<Row>()
                .height(3)
            })
            .collect_vec();

        let header = [
            Text::from("\nTxn Index\n").right_aligned(),
            Text::from("\nTxn Hash\n"),
        ]
        .into_iter()
        .map(Cell::from)
        .collect::<Row>()
        .height(3);

        let bar = " █ ";
        let t = Table::new(rows, [Constraint::Length(9), Constraint::Fill(u16::MAX)])
            .header(header)
            .row_highlight_style(Style::default().add_modifier(Modifier::REVERSED))
            .highlight_symbol(Text::from(vec!["".into(), bar.into(), "".into()]))
            .column_spacing(2)
            .highlight_spacing(HighlightSpacing::Always);

        frame.render_stateful_widget(t, area, table_state);
    }
}
