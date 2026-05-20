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

#[cfg(feature = "cmake")]
pub use self::cmake::{MonadCMake, MonadCMakeLinkage};

#[cfg(feature = "cmake")]
mod cmake;

#[cfg(feature = "metadata")]
pub fn repository_root() -> std::path::PathBuf {
    let metadata = cargo_metadata::MetadataCommand::new()
        .exec()
        .expect("Failed to get cargo metadata");

    let workspace_root = metadata.workspace_root.as_std_path();
    assert_eq!(
        workspace_root.file_name().and_then(|n| n.to_str()),
        Some("rust"),
        "Failed to verify workspace root is named 'rust', got: {}",
        workspace_root.display()
    );

    let repository_root = workspace_root
        .parent()
        .expect("Failed to get repository root from workspace root")
        .to_path_buf();

    let category_dir = repository_root.join("category");
    assert!(
        category_dir.exists(),
        "Failed to find category directory at {}",
        category_dir.display()
    );

    repository_root
}

pub fn should_build_execution() -> bool {
    println!("cargo:rerun-if-env-changed=TRIEDB_TARGET");

    std::env::var("TRIEDB_TARGET").is_ok_and(|target| target == "triedb_driver")
}

pub fn execution_dir() -> Option<String> {
    if !should_build_execution() {
        return None;
    }

    Some(
        std::env::var("DEP_MONAD_EXECUTION_CMAKE_BINARY_DIR")
            .expect("DEP_MONAD_EXECUTION_CMAKE_BINARY_DIR not set"),
    )
}
