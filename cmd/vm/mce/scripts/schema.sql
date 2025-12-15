-- SQL schema for the mce compile-time data

-- Create terminator type
CREATE TYPE terminator_type AS ENUM (
  'JumpI',
  'Return',
  'Revert',
  'Jump',
  'SelfDestruct',
  'Stop',
  'FallThrough',
  'InvalidInstruction'
);

-- Mapping between opcode and opcode name
CREATE TABLE IF NOT EXISTS opcodes (
  code INTEGER PRIMARY KEY,
  name TEXT NOT NULL
);

-- Insert opcode data
INSERT INTO opcodes (code, name) VALUES
('0x01'::float::numeric,  'Add'),
('0x02'::float::numeric,  'Mul'),
('0x03'::float::numeric,  'Sub'),
('0x04'::float::numeric,  'Div'),
('0x05'::float::numeric,  'SDiv'),
('0x06'::float::numeric,  'Mod'),
('0x07'::float::numeric,  'SMod'),
('0x08'::float::numeric,  'AddMod'),
('0x09'::float::numeric,  'MulMod'),
('0x0A'::float::numeric,  'Exp'),
('0x0B'::float::numeric,  'SignExtend'),
('0x10'::float::numeric,  'Lt'),
('0x11'::float::numeric,  'Gt'),
('0x12'::float::numeric,  'SLt'),
('0x13'::float::numeric,  'SGt'),
('0x14'::float::numeric,  'Eq'),
('0x15'::float::numeric,  'IsZero'),
('0x16'::float::numeric,  'And'),
('0x17'::float::numeric,  'Or'),
('0x18'::float::numeric,  'Xor'),
('0x19'::float::numeric,  'Not'),
('0x1A'::float::numeric,  'Byte'),
('0x1B'::float::numeric,  'Shl'),
('0x1C'::float::numeric,  'Shr'),
('0x1D'::float::numeric,  'Sar'),
('0x20'::float::numeric,  'Sha3'),
('0x30'::float::numeric,  'Address'),
('0x31'::float::numeric,  'Balance'),
('0x32'::float::numeric,  'Origin'),
('0x33'::float::numeric,  'Caller'),
('0x34'::float::numeric,  'CallValue'),
('0x35'::float::numeric,  'CallDataLoad'),
('0x36'::float::numeric,  'CallDataSize'),
('0x37'::float::numeric,  'CallDataCopy'),
('0x38'::float::numeric,  'CodeSize'),
('0x39'::float::numeric,  'CodeCopy'),
('0x3A'::float::numeric,  'GasPrice'),
('0x3B'::float::numeric,  'ExtCodeSize'),
('0x3C'::float::numeric,  'ExtCodeCopy'),
('0x3D'::float::numeric,  'ReturnDataSize'),
('0x3E'::float::numeric,  'ReturnDataCopy'),
('0x3F'::float::numeric,  'ExtCodeHash'),
('0x40'::float::numeric,  'BlockHash'),
('0x41'::float::numeric,  'Coinbase'),
('0x42'::float::numeric,  'Timestamp'),
('0x43'::float::numeric,  'Number'),
('0x44'::float::numeric,  'Difficulty'),
('0x45'::float::numeric,  'GasLimit'),
('0x46'::float::numeric,  'ChainId'),
('0x47'::float::numeric,  'SelfBalance'),
('0x48'::float::numeric,  'BaseFee'),
('0x49'::float::numeric,  'BlobHash'),
('0x4A'::float::numeric,  'BlobBaseFee'),
('0x50'::float::numeric,  'Pop'),
('0x51'::float::numeric,  'MLoad'),
('0x52'::float::numeric,  'MStore'),
('0x53'::float::numeric,  'MStore8'),
('0x54'::float::numeric,  'SLoad'),
('0x55'::float::numeric,  'SStore'),
('0x56'::float::numeric,  'Jump'),
('0x57'::float::numeric,  'JumpI'),
('0x58'::float::numeric,  'Pc'),
('0x59'::float::numeric,  'MSize'),
('0x5A'::float::numeric,  'Gas'),
('0x5B'::float::numeric,  'JumpDest'),
('0x5C'::float::numeric,  'TLoad'),
('0x5D'::float::numeric,  'TStore'),
('0x5E'::float::numeric,  'MCopy'),
('0x5F'::float::numeric,  'Push0'),
('0x60'::float::numeric,  'Push1'),
('0x61'::float::numeric,  'Push2'),
('0x62'::float::numeric,  'Push3'),
('0x63'::float::numeric,  'Push4'),
('0x64'::float::numeric,  'Push5'),
('0x65'::float::numeric,  'Push6'),
('0x66'::float::numeric,  'Push7'),
('0x67'::float::numeric,  'Push8'),
('0x68'::float::numeric,  'Push9'),
('0x69'::float::numeric,  'Push10'),
('0x6A'::float::numeric,  'Push11'),
('0x6B'::float::numeric,  'Push12'),
('0x6C'::float::numeric,  'Push13'),
('0x6D'::float::numeric,  'Push14'),
('0x6E'::float::numeric,  'Push15'),
('0x6F'::float::numeric,  'Push16'),
('0x70'::float::numeric,  'Push17'),
('0x71'::float::numeric,  'Push18'),
('0x72'::float::numeric,  'Push19'),
('0x73'::float::numeric,  'Push20'),
('0x74'::float::numeric,  'Push21'),
('0x75'::float::numeric,  'Push22'),
('0x76'::float::numeric,  'Push23'),
('0x77'::float::numeric,  'Push24'),
('0x78'::float::numeric,  'Push25'),
('0x79'::float::numeric,  'Push26'),
('0x7A'::float::numeric,  'Push27'),
('0x7B'::float::numeric,  'Push28'),
('0x7C'::float::numeric,  'Push29'),
('0x7D'::float::numeric,  'Push30'),
('0x7E'::float::numeric,  'Push31'),
('0x7F'::float::numeric,  'Push32'),
('0x80'::float::numeric,  'Dup1'),
('0x81'::float::numeric,  'Dup2'),
('0x82'::float::numeric,  'Dup3'),
('0x83'::float::numeric,  'Dup4'),
('0x84'::float::numeric,  'Dup5'),
('0x85'::float::numeric,  'Dup6'),
('0x86'::float::numeric,  'Dup7'),
('0x87'::float::numeric,  'Dup8'),
('0x88'::float::numeric,  'Dup9'),
('0x89'::float::numeric,  'Dup10'),
('0x8A'::float::numeric,  'Dup11'),
('0x8B'::float::numeric,  'Dup12'),
('0x8C'::float::numeric,  'Dup13'),
('0x8D'::float::numeric,  'Dup14'),
('0x8E'::float::numeric,  'Dup15'),
('0x8F'::float::numeric,  'Dup16'),
('0x90'::float::numeric,  'Swap1'),
('0x91'::float::numeric,  'Swap2'),
('0x92'::float::numeric,  'Swap3'),
('0x93'::float::numeric,  'Swap4'),
('0x94'::float::numeric,  'Swap5'),
('0x95'::float::numeric,  'Swap6'),
('0x96'::float::numeric,  'Swap7'),
('0x97'::float::numeric,  'Swap8'),
('0x98'::float::numeric,  'Swap9'),
('0x99'::float::numeric,  'Swap10'),
('0x9A'::float::numeric,  'Swap11'),
('0x9B'::float::numeric,  'Swap12'),
('0x9C'::float::numeric,  'Swap13'),
('0x9D'::float::numeric,  'Swap14'),
('0x9E'::float::numeric,  'Swap15'),
('0x9F'::float::numeric,  'Swap16'),
('0xA0'::float::numeric,  'Log0'),
('0xA1'::float::numeric,  'Log1'),
('0xA2'::float::numeric,  'Log2'),
('0xA3'::float::numeric,  'Log3'),
('0xA4'::float::numeric,  'Log4'),
('0xF0'::float::numeric,  'Create'),
('0xF1'::float::numeric,  'Call'),
('0xF2'::float::numeric,  'CallCode'),
('0xF3'::float::numeric,  'Return'),
('0xF4'::float::numeric,  'DelegateCall'),
('0xF5'::float::numeric,  'Create2'),
('0xFA'::float::numeric,  'StaticCall'),
('0xFD'::float::numeric,  'Revert'),
('0xFE'::float::numeric,  'Invalid'),
('0xFF'::float::numeric,  'SelfDestruct');

-- Smart contracts table
CREATE TABLE IF NOT EXISTS contracts (
  id SERIAL PRIMARY KEY,
  hash TEXT NOT NULL UNIQUE,
  code_size INTEGER NOT NULL,
  bytecode_size INTEGER NOT NULL
);

-- Smart contract addresses table
CREATE TABLE IF NOT EXISTS contract_addresses (
  id SERIAL PRIMARY KEY,
  contract_id INTEGER NOT NULL REFERENCES contracts(id),
  address TEXT NOT NULL UNIQUE
);

-- Smart contract have basic blocks
CREATE TABLE IF NOT EXISTS basic_blocks (
  id SERIAL PRIMARY KEY,
  contract_id INTEGER NOT NULL REFERENCES contracts(id),
  ix INTEGER NOT NULL, -- block index in the contract
  "offset" INTEGER NOT NULL, -- offset in the bytecode
  is_jumpdest BOOLEAN NOT NULL, -- basic block is a jumpdest
  terminator terminator_type NOT NULL,
  fallthrough_dest INTEGER NULL,
  code_size INTEGER NOT NULL,
  UNIQUE (contract_id, ix) -- Ensure unique blocks per contract
);

-- Basic block have instructions
CREATE TABLE IF NOT EXISTS instructions (
  id SERIAL PRIMARY KEY,
  block_id INTEGER NOT NULL REFERENCES basic_blocks(id),
  ix INTEGER NOT NULL, -- instruction index within the block
  opcode INTEGER NOT NULL, -- [0, 255]
  immediate TEXT NULL, -- For PUSH instructions
  code_size INTEGER NOT NULL -- Size of the instruction in bytes
);

-- Instructions have operands
CREATE TABLE IF NOT EXISTS instruction_operands (
  id SERIAL PRIMARY KEY,
  instruction_id INTEGER NOT NULL REFERENCES instructions(id),
  ix INTEGER NOT NULL, -- operand index
  literal TEXT NULL,
  general_reg INTEGER NULL,
  avx_reg INTEGER NULL,
  stack_offset INTEGER NULL,
  deferred_comparison BOOLEAN NULL,
  bit_upper_bound INTEGER NULL
);

-- Instructions have outputs
CREATE TABLE IF NOT EXISTS instruction_outputs (
  id SERIAL PRIMARY KEY,
  instruction_id INTEGER NOT NULL REFERENCES instructions(id),
  ix INTEGER NOT NULL, -- output index
  literal TEXT NULL,
  general_reg INTEGER NULL,
  avx_reg INTEGER NULL,
  stack_offset INTEGER NULL,
  deferred_comparison BOOLEAN NULL,
  bit_upper_bound INTEGER NULL
);

-- Create indices
CREATE INDEX idx_contracts_hash               ON contracts(hash);
CREATE INDEX idx_contract_address_contract_id ON contract_addresses(contract_id);
CREATE INDEX idx_blocks_contract_id           ON basic_blocks(contract_id);
CREATE INDEX idx_instructions_block_id_ix     ON instructions(block_id, ix);
CREATE INDEX idx_instruction_opcode           ON instructions(opcode);
CREATE INDEX idx_operands_instruction_id      ON instruction_operands(instruction_id);
CREATE INDEX idx_operands_instruction_id_lit  ON instruction_operands(instruction_id, literal);
CREATE INDEX idx_operands_instruction_id_ix   ON instruction_operands(instruction_id, ix);
CREATE INDEX idx_outputs_instruction_id       ON instruction_outputs(instruction_id);
CREATE INDEX idx_outputs_instruction_id_ix    ON instruction_outputs(instruction_id, ix);
CREATE INDEX idx_outputs_instruction_id_lit   ON instruction_outputs(instruction_id, literal);

-- Helper functions
CREATE OR REPLACE FUNCTION format_operands(literal_bound INTEGER, literal TEXT, avx_reg INTEGER, general_reg INTEGER, stack_offset INTEGER, deferred_comparison BOOLEAN)
RETURNS TEXT AS $$
BEGIN
  RETURN
    (SELECT
      CONCAT_WS('/',
        CASE (literal IS NOT NULL AND (literal_bound != -1 AND literal::float::numeric >= literal_bound))
          WHEN true THEN 'literal' ELSE NULL END,
        CASE (literal IS NOT NULL AND (literal_bound = -1 OR literal::float::numeric < literal_bound))
          WHEN true THEN literal::text ELSE NULL END,
        CASE (avx_reg IS NOT NULL
          AND literal IS NULL)
          WHEN true THEN 'AVX' ELSE NULL END,
        CASE (general_reg IS NOT NULL
          AND avx_reg IS NULL AND literal IS NULL)
          WHEN true THEN 'GPR' ELSE NULL END,
        CASE (stack_offset IS NOT NULL
          AND general_reg IS NULL AND avx_reg IS NULL AND literal IS NULL)
          WHEN true THEN 'STACK' ELSE NULL END,
        CASE (deferred_comparison IS NOT NULL AND deferred_comparison
          AND stack_offset IS NULL AND general_reg IS NULL AND avx_reg IS NULL AND literal IS NULL)
          WHEN true THEN 'EFLAGS' ELSE NULL END
      ));
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION get_instruction_inputs(iid INTEGER)
RETURNS JSONB AS $$
BEGIN
  RETURN (
    SELECT jsonb_agg(
      format_operands(0, o.literal, o.avx_reg, o.general_reg, o.stack_offset, o.deferred_comparison)
      ORDER BY ix DESC
    )
    FROM instruction_operands o
    WHERE o.instruction_id = iid
    );
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION get_instruction_inputs_small_literals(iid INTEGER, bound INTEGER)
RETURNS JSONB AS $$
BEGIN
  RETURN (
    SELECT jsonb_agg(
      format_operands(bound, o.literal, o.avx_reg, o.general_reg, o.stack_offset, o.deferred_comparison)
      ORDER BY ix DESC
    )
    FROM instruction_operands o
    WHERE o.instruction_id = iid
    );
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION get_instruction_outputs(iid INTEGER)
RETURNS JSONB AS $$
BEGIN
  RETURN (
    SELECT jsonb_agg(
      format_operands(0, o.literal, o.avx_reg, o.general_reg, o.stack_offset, o.deferred_comparison)
      ORDER BY ix DESC
    )
    FROM instruction_outputs o
    WHERE o.instruction_id = iid
    );
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION get_instruction_name(opcode INTEGER)
RETURNS TEXT AS $$
BEGIN
  RETURN (
    SELECT o.name FROM opcodes o WHERE o.code = opcode
    );
END;
$$ LANGUAGE plpgsql;

CREATE OR REPLACE FUNCTION get_opcode(opname TEXT)
RETURNS INTEGER AS $$
BEGIN
  RETURN (
    SELECT o.code FROM opcodes o WHERE UPPER(o.name) = UPPER(opname)
    );
END;
$$ LANGUAGE plpgsql;
