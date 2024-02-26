#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/fmt/receipt_fmt.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>

#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

using current_fork = fork_traits::shanghai;

static constexpr auto beneficiary =
    0x388C818CA8B9251b393131C08a736A67ccB19297_address;
static constexpr uint256_t base_fee_per_gas = 1'000'000'000u;
std::string global_value;

static Address addresses[100] = {
    0x76B1368Fb64770250929C65Ee5B9f79b21619746_address,
    0x95D8f330AcB39b0D5D1995c29a684f3cCe43835D_address,
    0xC68134F16B7532D4f4Beb178332Eb6AaAb411404_address,
    0x7065bc2340C3c018A945dE9c0A26D4557A49B5d9_address,
    0x6292C2C76DBE294990704CACbd0399c2D8094260_address,
    0xD2a48F2054190148caCAb6c14Df12D4326f55489_address,
    0xA6d8e7C288232Bb6D36013285b05915c1e368Bd0_address,
    0x1c72c06bEeb0987a53ccd589c58DFbE260a23B05_address,
    0xFb31224d89E67bc9CE6bA07AAFFb0eef3d02f2A8_address,
    0x5CaE1B8993c6818E5D7a02c762753feCA2051992_address,
    0x3a75EcF2090A5fBb5078c8406b08525Fa6D574f3_address,
    0x875aDF6e05905C9acd5fa313b231545974cbf6b1_address,
    0x55ac0Ea78C33186ae68f55449639B246cB55F6fE_address,
    0xFBc9c5e341b32B689657B0234E78a122CC4905F8_address,
    0x3d3B7B9d2DC6EF13E5B67A71C79b9F9d2Ea57326_address,
    0x5fFec43Af8e04b4BaF43c294A6385f7955a4D4D6_address,
    0x6F50B994F57e332Bb2cFCf6B1D9ef24297D9CE20_address,
    0x222346439c7834BAEcDbD69D7Db961758C37e280_address,
    0x5d65ae0d840b6086B87833805707e4E605c2939a_address,
    0xc865E9aD5954Ad45B2C3a3E485cB8C36D5B57624_address,
    0x2272EEB2a33723E8D5f7bF95d5631f86C68e70b2_address,
    0x5c83E6Eea6fDAcFA13F0C2472FF8aD4a99eCF557_address,
    0x23A7d9DAe4b1f4a2da45A43706463823B561abD4_address,
    0xCAF522Cc6c1D3b5286A3a9e243cDEfeA8aC9363f_address,
    0xbe821816BcC721441E1BB3848BB81eFA31012A2a_address,
    0x658397033768255537a2f2D45bA3D833d11e0d9D_address,
    0x903c7ED51260B4Ffd6768451c69a0CEaf9891F8a_address,
    0x3A70461B7B79Beb99b83c6D639268e03664A6B5B_address,
    0x5653E4FF0C1a6D1841635F13a27d25C3ae1a6671_address,
    0x3FB918c57Dd42150Dd40865e9F7Fe5E7Ad8BcbEe_address,
    0xDEca4c8e96ee9598319Bf1529b4ACdd6df22155D_address,
    0xa2784083fe1F0240f010b3D9E5A2CF1aeF9B449B_address,
    0x7d599279E9606fCd8278fb1D8a9B1BC5105D941C_address,
    0x67572D073B022576c90b20d5972078782412F5cC_address,
    0xbBB31D47D218bD257CaeB7Abd4fD46A40644F739_address,
    0x642d583bc5c36B0840A975Aed5446E8e473c3340_address,
    0xA95EFBaC6F1B4EE8f6b2bBd4b45C61c2897912F4_address,
    0x166f6B4532AdEBa3a779f41D9810C0EbAEFc64F2_address,
    0x6B92265A0bD7E531204cc05eC7253AE46d480377_address,
    0xfa8fDcD613491ED214b2E6bf18950Db9D354F2fc_address,
    0x6E460b504c96EdEB1373B9caB23905b40133f55b_address,
    0x415f7ffdbAF07d87f387a0ff4b2d73AD310A78B6_address,
    0x06eb3C8D8dAFd5FC880B39cA29F5059D2620b61A_address,
    0x2AABD8a6006B138Ef1933d36b86d6A88F70c8E69_address,
    0x038b6a02dF9dcF2e25FC315903b338aFAd4F4D16_address,
    0x7E0D913eAEC8109D7Bb4DaF8dA606853f51d9849_address,
    0x354c1BfD8ac5264C5a2036a634aE54a12217a6a7_address,
    0xb0C1B61199D3E2d1b6Ca6fA2E3931fAaF723A4a1_address,
    0x6E4385b9BA7f30b2ac5070aFc65DbFD86522a799_address,
    0x58cAdA2e9142715733483BF43347DCc548Ba6900_address,
    0x8358BC53849455238Eb483c933806d66936B89Ab_address,
    0x373380C8d49DeF9EE4D847B42fb865b36b33A25f_address,
    0x85A9AE6439839ba5D845b568a001B23aC5E8da7e_address,
    0xdc514a97f716Bd2c3eE39f2E36944208372B9523_address,
    0xDcB2F4cc37e4358B23eDC6Ab6Ff18723A9B06825_address,
    0x2cB36e0A82151224C489034cCCe0afBf3fc351a1_address,
    0x594f967C8431d60f130E6F55E24038621d8380Fc_address,
    0xa46773fFDc95bA27944464f7E433211f83c8503c_address,
    0x2897Bfd964B5b05C1799C1A781671B6057165d2B_address,
    0x0f91ebc80dB672139056f3D7378BCE9230C569da_address,
    0x79eEE01Baf31fF95E167b33eA5486fdB0D8e72f9_address,
    0x601e779F9769e006a7C1d36E58af4533b402Da81_address,
    0x729089D70a6Cd24fAE27c9c2d830441BEac71948_address,
    0xE6a07847f69ece81ec7218a1926d4b5f8634B12b_address,
    0xDFe66307C70Bbd5F9904C83476c2f54b9Da223fF_address,
    0x80269F94Eb511f411E941e39C7f0F2bE3406241c_address,
    0x86cc09045F14B38361293eA49807F25bfBE6Bb0c_address,
    0x7ED86cFafa204045a74E199d194e459380b66e89_address,
    0x8de70249c7b23Cb37d878E3b576bDd3B170a2a14_address,
    0x0d520d0f24134E9F472F2ed68b9e3B0D24e326DD_address,
    0xB47BA52394494e4b81EF7D7c3151B23f40346C49_address,
    0x04303Be0741d51A60FB15cD887c358bc2f6EDe88_address,
    0xeC88BDda0874bD538c44363f35124588a588B7A0_address,
    0x16f23B99c0fB36E55BB61Ac82d0eaF62612bcb6D_address,
    0x11f04D655CAf010F8bb0A02FA203565c38e99981_address,
    0x73fd038ef88EA813505138aDD09f6c9049ccFd8E_address,
    0xf7dB22918b8aadfFD977f142155f39994617C264_address,
    0xd443266CF5C52Fc8db834E48BdF0E6039bFBAA77_address,
    0x9C2015366aDf3b596FBA93b7f7f58a190376f4E4_address,
    0xD4478231280C30D12fddDC80ad1c1364FC88b3aA_address,
    0x1Fb163c15799d21F056B1e14f735abE6a6337177_address,
    0xA62bb2e2cF0Bb110dc8AEE2F13F54fC92070429C_address,
    0x222ee71ae757cC14EB116De6cA5523B9FC389E3C_address,
    0x0fa052E28CBc75533AC5855B19C04B06584d3C43_address,
    0x2239F14F98df44e5CCAe75299c5D030D99fc3322_address,
    0x3A70712611AC114AD31a70911A660EeeaBa845F8_address,
    0x68FEAdcE229adFAb9870caB12dCfd3bc0fd36383_address,
    0x377F99525bFfB9d7D0530369818c5f7dE31E7A90_address,
    0x6e6f1db6C590A11BE171D850524ba91432eC59Cb_address,
    0x6E22b804Fb5d371325A1C02f78EC8D4411E61459_address,
    0x0b4eA5355d9F479C53D2d285C6F1f7EF5b8844a6_address,
    0xAf0BE97B12754DdE34D93270C4d20A9cd4f3532d_address,
    0xC73Ff6b95E67AF695D2a17E5f2Fb0eeE644B6ffb_address,
    0x63B761ae99563dF5A73d642D14AC380C03a16beE_address,
    0x0D90C0807d1Ddb354a2ea8D757E7Bb58395E79bd_address,
    0x383dAbe73876A99724a2b9251191011581A13bb7_address,
    0x5210Db4f375Fa0b8aDECE354FB4EDE03073940Df_address,
    0x829536424e67029B275B313f397ebcfc897dF81c_address,
    0xa1C6fDae7211990428E3824BB7285FFd00Cc2217_address,
    0x45bC91896EF48A9484D7DF43322C5504AF1491c8_address};

std::optional<byte_string_view>
get(std::filesystem::path const &path, bool const setup, uint64_t const num)
{
    std::string filename;

    if (MONAD_UNLIKELY(setup)) {
        filename = "setup.bin";
    }
    else {
        filename = "transaction-" + std::to_string(num) + ".bin";
    }
    std::ifstream in{path / filename, std::ios::in | std::ios::binary};
    if (!in) {
        return std::nullopt;
    }

    in.seekg(0, std::ios::end);
    auto const pos = in.tellg();
    MONAD_ASSERT(pos >= 0);
    global_value.resize(static_cast<size_t>(pos));
    in.seekg(0, std::ios::beg);
    in.read(
        &global_value[0], static_cast<std::streamsize>(global_value.size()));
    in.close();

    auto const view = to_byte_string_view(global_value);

    return view;
}

Block make_block(byte_string_view &encoded_txns)
{
    Block block;
    BlockHeader block_header;
    block_header.beneficiary = beneficiary;
    block_header.base_fee_per_gas = std::make_optional(base_fee_per_gas);

    auto txns = rlp::decode_transaction_vector(encoded_txns);
    if (txns.has_error()) {
        LOG_INFO("Decode error: {}", txns.assume_error().value());
    }
    MONAD_ASSERT(!txns.has_error());

    block.transactions = std::move(txns.value());

    return block;
}

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"lob"};

    std::filesystem::path block_db_path{};
    uint64_t finish_batch = 1500;

    bool on_disk = false;
    bool compaction = false;
    unsigned nthreads = 4;
    unsigned nfibers = 4;
    auto sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    std::vector<std::filesystem::path> dbname_paths;
    int64_t file_size_db = 512; // 512GB

    quill::start(true);

    auto log_level = quill::LogLevel::Info;
    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();

    cli.add_option(
        "--finish_batch", finish_batch, "Last batch of txn to execute");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_flag("--on_disk", on_disk, "config TrieDb to be on disk");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "io_uring sq_thread_cpu field in io_uring_params");
    cli.add_option(
        "--dbname_paths",
        dbname_paths,
        "a list of db paths separated by comma, can config storage pool "
        "with 1 or more files/devices, will config on_disk triedb with "
        "anonymous inode if empty");
    cli.add_option(
        "--file_size_db",
        file_size_db,
        "size of each db file, only apply to newly created files but not "
        "existing files or raw blkdev");

    try {
        cli.parse(argc, argv);
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
        return cli.exit(e);
    }
    quill::get_root_logger()->set_log_level(log_level);

    auto block_db = BlockDb(block_db_path);
    auto const config = on_disk ? std::make_optional(mpt::OnDiskDbConfig{
                                      .append = false,
                                      .compaction = compaction,
                                      .rd_buffers = 8192,
                                      .wr_buffers = 32,
                                      .uring_entries = 128,
                                      .sq_thread_cpu = sq_thread_cpu,
                                      .dbname_paths = dbname_paths,
                                      .file_size_db = file_size_db})
                                : std::nullopt;
    auto db = db::TrieDb{config};
    LOG_INFO(
        "Running with block_db = {}, finish batch = {}",
        block_db_path,
        finish_batch);

    fiber::PriorityPool priority_pool{nthreads, nfibers};

    // Deposit balance
    {
        BlockState block_state{db};
        State state{block_state};
        for (auto const &address : addresses) {
            state.add_to_balance(
                address, base_fee_per_gas * base_fee_per_gas * 10'000u);
        }
        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
        block_state.commit();
    }

    LOG_INFO("Finished adding balance to relevant accounts");

    // execute setup txns
    {
        auto block_byte_string = get(block_db_path, /*setup*/ true, 0);
        MONAD_ASSERT(block_byte_string);
        Block setup_block = make_block(block_byte_string.value());
        BlockHashBuffer buffer;
        BlockState block_state{db};
        uint64_t cumulative_gas_used = 0u;
        auto const receipts = execute_block_no_post_validate<EVMC_SHANGHAI>(
            setup_block,
            buffer,
            priority_pool,
            block_state,
            cumulative_gas_used);
        block_state.commit();
    }

    LOG_INFO("Finished executing setup transactions");
    auto const start_time = std::chrono::steady_clock::now();

    // execute other txns

    for (uint64_t i = 0; i < std::min(finish_batch, uint64_t{1500}); ++i) {
        auto block_byte_string = get(block_db_path, /*setup*/ false, i);
        MONAD_ASSERT(block_byte_string);
        Block setup_block = make_block(block_byte_string.value());
        BlockHashBuffer buffer;
        BlockState block_state{db};
        uint64_t cumulative_gas_used = 0u;
        auto const receipts = execute_block_no_post_validate<EVMC_SHANGHAI>(
            setup_block,
            buffer,
            priority_pool,
            block_state,
            cumulative_gas_used);
        block_state.commit();
        LOG_INFO("At file {}", i);

        for (auto const &receipt : receipts.value()) {
            if (receipt.status != 1) {
                LOG_ERROR("Error receipt: {}", receipt);
            }
        }
    }

    auto const finish_time = std::chrono::steady_clock::now();
    auto const time_elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        finish_time - start_time);

    auto const num = db.count();

    LOG_INFO(
        "Finished running, num files = {}, num transactions = {}k, time "
        "elasped = {}, tps = {}",
        std::min(finish_batch, uint64_t{1500}),
        std::min(finish_batch, uint64_t{1500}),
        time_elapsed,
        finish_batch * 1000 /
            std::max(1UL, static_cast<uint64_t>(time_elapsed.count())));

    LOG_INFO(
        "Number of accounts = {}, number of storage = {}",
        num.first,
        num.second);

    return 0;
}
