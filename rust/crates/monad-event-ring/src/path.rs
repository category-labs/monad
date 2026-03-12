// Copyright (C) 2025-26 Category Labs, Inc.
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
    fs::File,
    path::{Path, PathBuf},
};

use crate::ffi;

/// A resolved event ring path that can be used to open event rings.
#[derive(Debug, Default)]
pub struct EventRingPath {
    path: PathBuf,
}

impl EventRingPath {
    /// Resolves the provided path.
    pub fn resolve(path: impl AsRef<Path>) -> Result<Self, String> {
        let path = ffi::monad_event_resolve_ring_path(path)?;

        Ok(Self { path })
    }

    /// Resolves the provided path using the provided basepath.
    pub fn resolve_with_default_path(
        path: impl AsRef<Path>,
        basepath: impl AsRef<Path>,
    ) -> Result<Self, String> {
        let path = ffi::monad_event_resolve_ring_path_with_basepath(Some(basepath), path)?;

        Ok(Self { path })
    }

    /// Opens the file at this path.
    pub fn open(&self) -> std::io::Result<File> {
        File::open(&self.path)
    }

    /// Returns true if the file at this path is likely to be an event ring snapshot file.
    pub fn is_snapshot_file(&self) -> Result<bool, String> {
        let file = self.open().map_err(|err| err.to_string())?;

        ffi::monad_event_is_snapshot_file(&file, self.as_error_name())
    }

    pub(crate) fn as_error_name(&self) -> String {
        self.path.display().to_string()
    }
}

impl AsRef<EventRingPath> for EventRingPath {
    fn as_ref(&self) -> &EventRingPath {
        self
    }
}
