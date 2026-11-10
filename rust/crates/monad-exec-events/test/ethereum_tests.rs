mod harness;

use std::collections::BTreeMap;

use harness::{EthereumTestCase, EthereumTestFork, ExecEventEthereumTestValidator, ETHEREUM_TESTS};
use include_dir::DirEntry;
use itertools::Itertools;
use libtest_mimic::{Arguments, Trial};

fn main() {
    let args = Arguments::from_args();
    let mut trials = Vec::new();

    let mut files = ETHEREUM_TESTS.files().collect_vec();

    let mut test_dirs = ETHEREUM_TESTS.dirs().collect_vec();

    while let Some(test_dir) = test_dirs.pop() {
        for test_dir_child in test_dir.entries() {
            match test_dir_child {
                DirEntry::Dir(test_dir) => test_dirs.push(test_dir),
                DirEntry::File(file) => files.push(file),
            }
        }
    }

    for file in files {
        let contents = file
            .contents_utf8()
            .unwrap_or_else(|| panic!("Ethereum test is not UTF-8: {}", file.path().display()));

        let Ok(tests) = serde_json::from_str::<BTreeMap<String, EthereumTestCase>>(contents) else {
            continue;
        };
        // .unwrap_or_else(|error| panic!("failed to parse {}: {error}", file.path().display()));

        for (name, test) in tests {
            let EthereumTestCase {
                info,
                env,
                post,
                pre,
                transaction,
            } = test;

            let post: BTreeMap<_, _> = post
                .into_iter()
                .filter(|(fork, _)| *fork == EthereumTestFork::Cancun)
                .collect();

            if post.is_empty()
                || post
                    .values()
                    .flatten()
                    .any(|state| state.expect_exception.is_some())
            {
                continue;
            }

            let test = EthereumTestCase {
                info,
                env,
                post,
                pre,
                transaction,
            };

            let test_name = format!("{}::{name}", file.path().display());

            trials.push(Trial::test(test_name, move || {
                let validator = ExecEventEthereumTestValidator::new();
                futures::executor::block_on(validator.validate(test));
                Ok(())
            }));
        }
    }

    assert!(!trials.is_empty(), "no supported Ethereum tests found");
    libtest_mimic::run(&args, trials).exit();
}
