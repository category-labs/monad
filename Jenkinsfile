pipeline {
  agent {
    label 'execution'
  }

  stages {
    stage('Checkout') {
      steps {
        cleanWs()

        sh 'git config --global url."https://github.com/".insteadOf git@github.com:'

        checkout([
          $class: 'GitSCM',
          branches: [[name: 'refs/heads/main']],
          doGenerateSubmoduleConfigurations: true,
          extensions: scm.extensions + [[
            $class: 'SubmoduleOption',
            recursiveSubmodules: true,
            parentCredentials: true
          ],[
            $class: 'CloneOption',
            shallow: true,
            noTags:  true,
            depth:   1,
            timeout: 100
          ]],
          submoduleCfg: [],
          userRemoteConfigs: [[credentialsId: 'github-credentials', url: 'https://github.com/monad-crypto/monad.git']]
        ])
      }
    }

    stage('Build replay_ethereum') {
      steps {
        script {
          writeFile file:
            'block_db.patch', text: '''
diff --git a/src/monad/db/block_db.cpp b/src/monad/db/block_db.cpp
index 0b852b6..2409589 100644
--- a/src/monad/db/block_db.cpp
+++ b/src/monad/db/block_db.cpp
@@ -25,7 +25,8 @@ BlockDb::BlockDb(std::filesystem::path const &dir)

 bool BlockDb::get(uint64_t const num, Block &block) const
 {
-    auto const key = std::to_string(num);
+    auto const folder = std::to_string(num / 1000000) + 'M';
+    auto const key = folder + '/' + std::to_string(num);
     auto const result = db_.get(key.c_str());
     if (!result.has_value()) {
         return false;
@@ -49,7 +50,8 @@ bool BlockDb::get(uint64_t const num, Block &block) const

 void BlockDb::upsert(uint64_t const num, Block const &block) const
 {
-    auto const key = std::to_string(num);
+    auto const folder = std::to_string(num / 1000000) + 'M';
+    auto const key = folder + '/' + std::to_string(num);
     auto const encoded_block = rlp::encode_block(block);
     size_t brotli_size = BrotliEncoderMaxCompressedSize(encoded_block.size());
     MONAD_ASSERT(brotli_size);
@@ -73,7 +75,8 @@ void BlockDb::upsert(uint64_t const num, Block const &block) const

 bool BlockDb::remove(uint64_t const num) const
 {
-    auto const key = std::to_string(num);
+    auto const folder = std::to_string(num / 1000000) + 'M';
+    auto const key = folder + '/' + std::to_string(num);
     return db_.remove(key.c_str());
 }
            '''
          // Patch monad/db/block_db.cpp
          sh(script: "/bin/bash -c 'patch -p1 < block_db.patch'")
          sh'''
            if [ ! -d ./state_db ]; then
              mkdir state_db
            else
              echo "./state_db exists; do nothing"
            fi

            export CC=clang-18
            export CXX=clang++-18
            export CMAKE_BUILD_TYPE=RelWithDebInfo
            export DISABLE_TESTS=0

            CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./monad-core/scripts/configure.sh

            VERBOSE=1 \
            cmake \
              --build build \
              --config RelWithDebInfo \
              --target all
            '''
        }
      }
    }

    stage('Replay 0->100k') {
      steps {
        script {
          sh'''
            truncate -s 512GB test.db
            ./build/monad-trie/monad_mpt --storage test.db --create
            ./build/src/monad/execution/ethereum/replay_ethereum \
              --block_db /home/jhunsaker/block_db/ \
              --genesis_file ./test/common/genesis/ethereum/mainnet.json \
              --finish 100001 \
              --db ./test.db
            '''
        }
      }
    }

    stage('Replay 12000000->12100001') {
      steps {
        script {
          sh'''
            rm test.db
            truncate -s 512GB test.db
            ./build/monad-trie/monad_mpt --storage test.db --create
            ln -sf /home/jhunsaker/checkpoints/12000000 ./state_db/12000000
            ./build/src/monad/execution/ethereum/replay_ethereum \
              --block_db /home/jhunsaker/block_db/ \
              --load_snapshot ./state_db/12000000 \
              --genesis_file ./test/common/genesis/ethereum/mainnet.json \
              --finish 12100001 \
              --db ./test.db
            '''
        }
      }
    }

    stage('Replay 15000000->15100001') {
      steps {
        script {
          sh'''
            rm test.db
            truncate -s 512GB test.db
            ./build/monad-trie/monad_mpt --storage test.db --create
            ln -sf /home/jhunsaker/checkpoints/15000000 ./state_db/15000000
            ./build/src/monad/execution/ethereum/replay_ethereum \
              --block_db /home/jhunsaker/block_db/ \
              --load_snapshot ./state_db/15000000 \
              --genesis_file ./test/common/genesis/ethereum/mainnet.json \
              --finish 15100001 \
              --db test.db
            '''
        }
      }
    }

  }
}

