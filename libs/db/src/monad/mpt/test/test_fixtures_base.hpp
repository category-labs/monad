#pragma once

#include <monad/mpt/compute.hpp>
#include <monad/mpt/trie.hpp>

#include <monad/core/assert.h>
#include <monad/core/small_prng.hpp>

#include <array>
#include <vector>

namespace monad::test
{
    using namespace monad::mpt;
    using namespace monad::literals;

    struct DummyComputeLeafData
    {
        // TEMPORARY for POC
        // compute leaf data as - concat(input_leaf, hash);
        static byte_string compute(Node const &node)
        {
            return byte_string{node.value()} + byte_string{node.data()};
        }
    };

    using MerkleCompute = ::monad::mpt::MerkleComputeBase<DummyComputeLeafData>;

    struct EmptyCompute final : Compute
    {
        virtual unsigned compute_len(
            std::span<ChildData>, uint16_t, NibblesView,
            std::optional<byte_string_view>) override
        {
            return 0;
        }

        virtual unsigned compute_branch(unsigned char *, Node *) override
        {
            return 0;
        }

        virtual unsigned compute(unsigned char *, Node *) override
        {
            return 0;
        }
    };

    struct RootMerkleCompute : public MerkleCompute
    {
        virtual unsigned compute(unsigned char *const, Node *const) override
        {
            return 0;
        }
    };

    class StateMachineWithBlockNo final : public StateMachine
    {
    private:
        static constexpr auto block_num_size = BLOCK_NUM_NIBBLES_LEN;
        static constexpr auto cache_depth = block_num_size + 6;
        static constexpr auto max_depth = block_num_size + 64 + 64;
        size_t depth{0};

    public:
        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<StateMachineWithBlockNo>(*this);
        }

        virtual void down(unsigned char) override
        {
            ++depth;
        }

        virtual void up(size_t n) override
        {
            MONAD_DEBUG_ASSERT(n <= depth);
            depth -= n;
        }

        virtual Compute &get_compute() const override
        {
            static MerkleCompute m{};
            static RootMerkleCompute rm{};
            static EmptyCompute e{};
            if (MONAD_LIKELY(depth > block_num_size)) {
                return m;
            }
            else if (depth < block_num_size) {
                return e;
            }
            return rm;
        }

        virtual constexpr bool cache() const override
        {
            MONAD_ASSERT(depth <= max_depth);
            return depth < cache_depth;
        }

        virtual constexpr bool compact() const override
        {
            return depth >= block_num_size;
        }
    };

    static_assert(sizeof(StateMachineWithBlockNo) == 16);
    static_assert(alignof(StateMachineWithBlockNo) == 8);

    class StateMachineVarLenTrieWithBlockNo final : public StateMachine
    {
    private:
        static constexpr auto block_num_size = BLOCK_NUM_NIBBLES_LEN;
        static constexpr auto cache_depth = block_num_size + 6;
        static constexpr auto max_depth = block_num_size + 65;
        size_t depth{0};

    public:
        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<StateMachineVarLenTrieWithBlockNo>(*this);
        }

        virtual void down(unsigned char) override
        {
            ++depth;
        }

        virtual void up(size_t n) override
        {
            MONAD_DEBUG_ASSERT(n <= depth);
            depth -= n;
        }

        virtual Compute &get_compute() const override
        {
            static VarLenMerkleCompute m{};
            static RootVarLenMerkleCompute rm{};
            static EmptyCompute e{};
            if (MONAD_LIKELY(depth > block_num_size)) {
                return m;
            }
            else if (depth < block_num_size) {
                return e;
            }
            return rm;
        }

        virtual constexpr bool cache() const override
        {
            MONAD_ASSERT(depth <= max_depth);
            return depth < cache_depth;
        }

        virtual constexpr bool compact() const override
        {
            return depth >= block_num_size;
        }
    };

    static_assert(sizeof(StateMachineVarLenTrieWithBlockNo) == 16);
    static_assert(alignof(StateMachineVarLenTrieWithBlockNo) == 8);

    template <class Compute, size_t cache_depth = 6>
    class StateMachineAlways final : public StateMachine
    {
    private:
        size_t depth{0};

    public:
        StateMachineAlways() = default;

        virtual std::unique_ptr<StateMachine> clone() const override
        {
            return std::make_unique<StateMachineAlways<Compute, cache_depth>>(
                *this);
        }

        virtual void down(unsigned char) override
        {
            ++depth;
        }

        virtual void up(size_t n) override
        {
            MONAD_DEBUG_ASSERT(n <= depth);
            depth -= n;
        }

        virtual Compute &get_compute() const override
        {
            static Compute c{};
            return c;
        }

        virtual constexpr bool cache() const override
        {
            return depth < cache_depth;
        }

        virtual constexpr bool compact() const override
        {
            return false;
        }
    };

    using StateMachineAlwaysEmpty = StateMachineAlways<EmptyCompute>;
    using StateMachineAlwaysMerkle = StateMachineAlways<MerkleCompute>;
    using StateMachineAlwaysVarLen = StateMachineAlways<VarLenMerkleCompute>;

    Node::UniquePtr upsert_vector(
        UpdateAuxImpl &aux, StateMachine &sm, Node::UniquePtr old,
        std::vector<Update> &&update_vec)
    {
        UpdateList update_ls;
        for (auto &it : update_vec) {
            update_ls.push_front(it);
        }
        return upsert(aux, sm, std::move(old), std::move(update_ls));
    }

    template <class... Updates>
    [[nodiscard]] constexpr Node::UniquePtr upsert_updates(
        UpdateAuxImpl &aux, StateMachine &sm, Node::UniquePtr old,
        Updates... updates)
    {
        UpdateList update_ls;
        (update_ls.push_front(updates), ...);
        return upsert(aux, sm, std::move(old), std::move(update_ls));
    }

    namespace fixed_updates
    {
        std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
            {0x1234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex},
            {0x1234567822345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebabe_hex},
            {0x1234567832345678123456781234567812345678123456781234567812345671_hex,
             0xdeadcafedeadcafedeadcafedeadcafedeadcafedeadcafedeadcafedeadcafe_hex},
            {0x1234567832345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbabedeadbabedeadbabedeadbabedeadbabedeadbabedeadbabedeadbabe_hex}};
    };

    namespace unrelated_leaves
    {
        std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
            {0x0234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef_hex},
            {0x1234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebabe_hex},
            {0x2234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadcafedeadcafedeadcafedeadcafedeadcafedeadcafedeadcafedeadcafe_hex},
            {0x3234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbabedeadbabedeadbabedeadbabedeadbabedeadbabedeadbabedeadbabe_hex}};
    };

    namespace var_len_values
    {
        std::vector<std::pair<monad::byte_string, monad::byte_string>> const kv{
            {0x0234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdead_hex}, // 0
            {0x1234567812345678123456781234567812345678123456781234567812345678_hex,
             0xbeef_hex}, // 1
            {0x2234567812345678123456781234567812345678123456781234567812345678_hex,
             0xba_hex}, // 2
            {0x3234567812345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeef_hex}, // 3
            {0x1234567822345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbeefcafe_hex}, // 4
            {0x1234567832345678123456781234567812345678123456781234567812345671_hex,
             0xdeadcafedeadcafedeadcafedeadcafedead_hex}, // 5
            {0x1234567832345678123456781234567812345678123456781234567812345678_hex,
             0xdeadbabedeadbabedeadbabedead_hex}}; // 6
    };

    // merkle tries
    template <monad::mpt::lockable_or_void LockType, class Base>
    class InMemoryTrieBase : public Base
    {
    public:
        Node::UniquePtr root;
        UpdateAux<LockType> aux;

        InMemoryTrieBase()
            : root()
            , aux(nullptr)
        {
        }

        void reset()
        {
            root.reset();
        }

        constexpr bool on_disk() const
        {
            return aux.is_on_disk();
        }

        constexpr MONAD_ASYNC_NAMESPACE::storage_pool *get_storage_pool() const
        {
            return nullptr;
        }
    };

    template <monad::mpt::lockable_or_void LockType, class Base>
    class OnDiskTrieBase : public Base
    {
    private:
        monad::async::storage_pool pool{
            monad::async::use_anonymous_inode_tag{}};
        monad::io::Ring ring1, ring2;
        monad::io::Buffers rwbuf;
        MONAD_ASYNC_NAMESPACE::AsyncIO io;

    public:
        Node::UniquePtr root;
        UpdateAux<LockType> aux;

        OnDiskTrieBase()
            : ring1(2)
            , ring2(4)
            , rwbuf(monad::io::make_buffers_for_segregated_read_write(
                  ring1, ring2, 2, 4,
                  MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                  MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE))
            , io(pool, rwbuf)
            , root()
            , aux(&io)
        {
        }

        void reset()
        {
            root.reset();
        }

        constexpr bool on_disk() const
        {
            return aux.is_on_disk();
        }

        constexpr MONAD_ASYNC_NAMESPACE::storage_pool *get_storage_pool()
        {
            return &io.storage_pool();
        }
    };

    template <class Base>
    class MerkleTrie : public Base
    {
    public:
        std::unique_ptr<StateMachine> sm =
            std::make_unique<StateMachineAlwaysMerkle>();

        monad::byte_string root_hash()
        {
            if (this->root.get()) {
                monad::byte_string res(32, 0);
                auto const len = this->sm->get_compute().compute(
                    res.data(), this->root.get());
                if (len < KECCAK256_SIZE) {
                    keccak256(res.data(), len, res.data());
                }
                return res;
            }
            return empty_trie_hash;
        }
    };

    template <class Base>
    class PlainTrie : public Base
    {
    public:
        std::unique_ptr<StateMachine> sm =
            std::make_unique<StateMachineAlwaysEmpty>();
    };

    template <typename BaseTrie>
    class EraseFixture : public BaseTrie
    {
    public:
        EraseFixture()
            : BaseTrie()
        {
            auto const &kv = fixed_updates::kv;

            std::vector<Update> update_vec;
            std::ranges::transform(
                kv, std::back_inserter(update_vec), [](auto &su) -> Update {
                    auto &[k, v] = su;
                    return make_update(k, v);
                });
            this->root = upsert_vector(
                this->aux, *this->sm, nullptr, std::move(update_vec));
        }
    };

    struct FillDBWithChunksConfig
    {
        size_t chunks_to_fill;
        size_t chunks_max{64};
        bool alternate_slow_fast_writer{false};
        bool use_anonymous_inode{true};
    };

    template <
        FillDBWithChunksConfig Config, monad::mpt::lockable_or_void LockType,
        class Base>
    struct FillDBWithChunks : public Base
    {
        struct state_t
        {
            MONAD_ASYNC_NAMESPACE::storage_pool pool{[] {
                MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
                auto const bitpos =
                    std::countr_zero(MONAD_ASYNC_NAMESPACE::AsyncIO::
                                         MONAD_IO_BUFFERS_WRITE_SIZE);
                flags.chunk_capacity = bitpos;
                if constexpr (Config.use_anonymous_inode) {
                    return MONAD_ASYNC_NAMESPACE::storage_pool(
                        MONAD_ASYNC_NAMESPACE::use_anonymous_inode_tag{},
                        flags);
                }
                char temppath[] = "monad_test_fixture_XXXXXX";
                int const fd = mkstemp(temppath);
                if (-1 == fd) {
                    abort();
                }
                if (-1 ==
                    ftruncate(
                        fd,
                        Config.chunks_max * MONAD_ASYNC_NAMESPACE::AsyncIO::
                                                MONAD_IO_BUFFERS_WRITE_SIZE +
                            24576)) {
                    abort();
                }
                ::close(fd);
                std::filesystem::path temppath2(temppath);
                return MONAD_ASYNC_NAMESPACE::storage_pool(
                    {&temppath2, 1},
                    MONAD_ASYNC_NAMESPACE::storage_pool::mode::create_if_needed,
                    flags);
            }()};
            monad::io::Ring ring1{2};
            monad::io::Ring ring2{4};
            monad::io::Buffers rwbuf{
                monad::io::make_buffers_for_segregated_read_write(
                    ring1, ring2, 2, 4,
                    MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                    MONAD_ASYNC_NAMESPACE::AsyncIO::
                        MONAD_IO_BUFFERS_WRITE_SIZE)};
            MONAD_ASYNC_NAMESPACE::AsyncIO io{pool, rwbuf};
            MerkleCompute comp;
            Node::UniquePtr root;
            StateMachineAlwaysMerkle sm;
            UpdateAux<LockType> aux{&io}; // trie section starts from account
            monad::small_prng rand;
            std::vector<std::pair<monad::byte_string, size_t>> keys;

            state_t()
            {
                aux.alternate_slow_fast_node_writer_unit_testing_only(
                    Config.alternate_slow_fast_writer);
                ensure_total_chunks(Config.chunks_to_fill);
                std::cout << "After suite set up before testing:";
                print(std::cout);
            }

            ~state_t()
            {
                for (auto &device : pool.devices()) {
                    auto const path = device.current_path();
                    if (std::filesystem::exists(path)) {
                        std::filesystem::remove(path);
                    }
                }
            }

            std::ostream &print(std::ostream &s) const
            {
                auto v = pool.devices().front().capacity();
                std::cout << "\n   Storage pool capacity = " << v.first
                          << " consumed = " << v.second
                          << " chunks = " << pool.chunks(pool.seq);
                auto const diff =
                    (int64_t(aux.get_lower_bound_free_space()) -
                     int64_t(v.first - v.second));
                std::cout << "\n   DB thinks there is a lower bound of "
                          << aux.get_lower_bound_free_space()
                          << " bytes free whereas the syscall thinks there is "
                          << (v.first - v.second)
                          << " bytes free, which is a difference of " << diff
                          << ".\n";
                std::cout << "   Fast list:";
                for (auto const *ci = aux.db_metadata()->fast_list_begin();
                     ci != nullptr;
                     ci = ci->next(aux.db_metadata())) {
                    auto idx = ci->index(aux.db_metadata());
                    auto chunk = pool.chunk(pool.seq, idx);
                    std::cout << "\n      Chunk " << idx
                              << " has capacity = " << chunk->capacity()
                              << " consumed = " << chunk->size();
                }
                std::cout << "\n\n   Slow list:";
                for (auto const *ci = aux.db_metadata()->slow_list_begin();
                     ci != nullptr;
                     ci = ci->next(aux.db_metadata())) {
                    auto idx = ci->index(aux.db_metadata());
                    auto chunk = pool.chunk(pool.seq, idx);
                    std::cout << "\n      Chunk " << idx
                              << " has capacity = " << chunk->capacity()
                              << " consumed = " << chunk->size();
                }
                std::cout << "\n\n   Free list: "
                          << aux.db_metadata()->capacity_in_free_list
                          << " bytes.";
                std::cout << std::endl;
                return s;
            }

            void ensure_total_chunks(size_t chunks)
            {
                std::vector<Update> updates;
                updates.reserve(1000);
                for (;;) {
                    UpdateList update_ls;
                    updates.clear();
                    for (size_t n = 0; n < 1000; n++) {
                        {
                            monad::byte_string key(
                                0x1234567812345678123456781234567812345678123456781234567812345678_hex);
                            for (size_t n = 0; n < key.size(); n += 4) {
                                *(uint32_t *)(key.data() + n) = rand();
                            }
                            keys.emplace_back(
                                std::move(key), aux.get_root_offset().id);
                        }
                        updates.push_back(
                            make_update(keys.back().first, keys.back().first));
                        update_ls.push_front(updates.back());
                    }
                    root =
                        upsert(aux, sm, std::move(root), std::move(update_ls));
                    size_t count = 0;
                    for (auto const *ci = aux.db_metadata()->fast_list_begin();
                         ci != nullptr;
                         count++, ci = ci->next(aux.db_metadata())) {
                    }
                    if (count >= chunks) {
                        break;
                    }
                }
            }

            std::vector<
                std::pair<uint32_t, MONAD_MPT_NAMESPACE::detail::unsigned_20>>
            fast_list_ids() const
            {
                std::vector<std::pair<
                    uint32_t,
                    MONAD_MPT_NAMESPACE::detail::unsigned_20>>
                    ret;
                ret.reserve(4);
                for (auto const *ci = aux.db_metadata()->fast_list_begin();
                     ci != nullptr;
                     ci = ci->next(aux.db_metadata())) {
                    ret.emplace_back(
                        ci->index(aux.db_metadata()), ci->insertion_count());
                }
                return ret;
            }

            std::vector<
                std::pair<uint32_t, MONAD_MPT_NAMESPACE::detail::unsigned_20>>
            slow_list_ids() const
            {
                std::vector<std::pair<
                    uint32_t,
                    MONAD_MPT_NAMESPACE::detail::unsigned_20>>
                    ret;
                ret.reserve(4);
                for (auto const *ci = aux.db_metadata()->slow_list_begin();
                     ci != nullptr;
                     ci = ci->next(aux.db_metadata())) {
                    ret.emplace_back(
                        ci->index(aux.db_metadata()), ci->insertion_count());
                }
                return ret;
            }

            monad::byte_string root_hash()
            {
                if (this->root.get()) {
                    monad::byte_string res(32, 0);
                    this->sm.get_compute().compute(
                        res.data(), this->root.get());
                    return res;
                }
                return empty_trie_hash;
            }
        };

        static state_t *&state()
        {
            static state_t *v;
            return v;
        }

        static void SetUpTestSuite()
        {
            state() = new state_t;
        }

        static void TearDownTestSuite()
        {
            delete state();
        }
    };
}
