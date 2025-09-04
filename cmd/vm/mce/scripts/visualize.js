// MCE bytecode visualization tool.
// This script takes as input a JSON file produced with mce's -o option.

// Helper functions

// Colors used to highlight virtual stack entries that are the same
const colors = [ "DarkTurquoise", "MediumVioletRed", "Magenta", "DarkSeaGreen", "MediumTurquoise", "Chocolate", "Sienna", "Tan", "DarkOrange", "LightSeaGreen", "LightGreen", "Gold", "Red", "HotPink", "DarkGreen", "RebeccaPurple", "LightPink", "DarkSlateGray", "DarkBlue", "Coral", "DarkKhaki", "Aquamarine", "RosyBrown", "LightSteelBlue", "MediumPurple", "DarkCyan", "SlateGray", "LightSlateGray", "MediumSeaGreen", "LimeGreen", "GreenYellow", "CornflowerBlue", "Navy", "MediumAquaMarine", "LightGray", "MediumBlue", "Purple", "DarkMagenta", "Khaki", "SteelBlue", "Teal", "Pink", "LightSalmon", "DarkRed", "DodgerBlue", "DimGray", "DarkOrchid", "Cyan", "SeaGreen", "DarkOliveGreen", "DeepSkyBlue", "RoyalBlue", "SandyBrown", "Lime", "Chartreuse", "YellowGreen", "SlateBlue", "SaddleBrown", "Gray", "Brown", "LightCoral", "DarkViolet", "DarkGray", "MediumOrchid", "Aqua", "FireBrick", "Silver", "SkyBlue", "LightBlue", "Tomato", "Fuchsia", "Crimson", "NavajoWhite", "MediumSpringGreen", "GoldenRod", "PaleGoldenRod", "Yellow", "DarkGoldenRod", "Thistle", "Blue", "MidnightBlue", "LightSkyBlue", "LemonChiffon", "Plum", "PowderBlue", "Maroon", "MediumSlateBlue", "CadetBlue", "OrangeRed", "BlueViolet", "Green", "DarkSalmon", "Olive", "Peru", "Salmon", "IndianRed", "BurlyWood", "PaleGreen", "Black", "Violet", "LightGoldenRodYellow", "Wheat", "Turquoise", "PaleVioletRed", "ForestGreen", "DarkSlateBlue", "DeepPink", "LawnGreen", "SpringGreen", "Indigo", "Orange", "Orchid", "PaleTurquoise", "OliveDrab" ]

function suffix_length(char, str) {
  let count = 0;
  for (let i = str.length - 1; i >= 0; i--) {
    if (str[i] == char) {
      count++;
    } else {
      break;
    }
  }
  return count;
}

function immediate_to_str(imm) {
  if (imm !== undefined && imm.length != 0 && imm.length >= 8) {
    // If the last character of the immediate repeats more than 3 times,
    // truncate it.
    const l = suffix_length(imm[imm.length - 1], imm);
    if (l > 3) {
      return `${imm.slice(0, Math.max(5, -l + 1))}...`;
    } else {
      return `${imm}`;
    }
  } else {
    return imm;
  }
}

function parseHex(value) {
  if (typeof value === "string") {
    value = value.trim();
    if (value.startsWith("0x")) {
      return parseInt(value.slice(2), 16);
    }
  }
  return -1; // Not a valid hex string
}

// Entry point
function loadFile(event) {
  const file = event.target.files[0];
  const reader = new FileReader();
  reader.onload = (e) => {
    const json = JSON.parse(e.target.result);
    displayBasicBlocks(json);
  };
  reader.readAsText(file);
}

// For each basic block, create a div that will list the instructions
function displayBasicBlocks(blocks) {
  const displayDiv = document.getElementById("display");
  displayDiv.innerHTML = ""; // Clear previous content

  blocks.forEach((block, blockIndex) => {
    const blockDiv = displayBasicBlock(blocks, blockIndex, block);
    displayDiv.appendChild(blockDiv);
  });
}

function operand_location_to_str(loc) {
  // If the operand is a literal, we don't care about the other operands
  if (loc.literal) {
    return immediate_to_str(loc.literal);
  }

  // Otherwise, concatenate the locations together
  arr = []
  if (loc.avx_reg !== undefined) {
    arr.push(`AVX${loc.avx_reg}`);
  }
  if (loc.general_reg !== undefined) {
    arr.push(`GPR${loc.general_reg}`);
  }
  if (loc.stack_offset !== undefined) {
    arr.push(`STACK[${loc.stack_offset}]`);
  }
  if (loc.deferred_comparison !== undefined && loc.deferred_comparison) {
    arr.push(`EFLAGS`);
  }
  if (arr.length === 0) {
    return "UNKNOWN"; // This should not happen
  }

  return arr.join("/");
}

// Format the operand locations into a string representation.
function format_operand_locations(color_map, virtual_stack, loc) {
  // Assign a color if not already assigned
  const loc_str = operand_location_to_str(loc);
  // If it has a color and appears more than once in the virtual stack, color it
  if (virtual_stack.filter(x => operand_location_to_str(x) === loc_str).length > 1) {
    // If the color map has the location, use it
    if (color_map.has(loc_str)) {
      return `<span style="color: ${color_map.get(loc_str)}">${loc_str}</span>`;
    }
  }
  return `<span>${loc_str}</span>`;
}

// Traverse the operands and assign each unique location a color
function allocate_colors(operands) {
  const color_map = new Map();

  operands.forEach((loc) => {
    const loc_str = operand_location_to_str(loc);
    if (!color_map.has(loc_str)) {
      color_map.set(loc_str, colors[color_map.size % colors.length]);
    }
  });

  return color_map;
}

// Format the instruction name.
// For most instructions, this is equivalent to instr.opcode_name.toUpperCase().
// For PUSH/SWAP/DUP/LOG instructions, append the index and immediate value (push only).
function format_instruction_name(instr) {
  // Show the opcode name and immediate value (if any), convert to camel case
  var name = instr.opcode_name.toUpperCase();
  if (instr.index !== undefined) {
    name += `${instr.index}`;
  }

  if (instr.immediate !== undefined) {
    name += ` ${immediate_to_str(instr.immediate)}`;
  }

  return name;
}

// Find block with given offset. This is used to resolve known jump destinations.
function block_id_at_offset(blocks, offset) {
  for (let i = 0; i < blocks.length; i++) {
    if (blocks[i].offset === offset) {
      return i;
    }
  }
  return -1; // Not found
}

// For each instruction in the basic block, create a table entry that will show
// the operands, with one operand per column.
// Push instructions come with a literal value that is also displayed
function displayBasicBlock(blocks, block_id, block) {
  const blockDiv = document.createElement("div");
  blockDiv.id = `block-${block_id}`;
  blockDiv.className = "block";
  blockDiv.innerHTML = `<h2>Block ${block_id}</h2>`;

  const table = document.createElement("table");
  const headerRow = document.createElement("tr");
  headerRow.innerHTML = "<th>PC</th><th>Instruction</th><th>Stack</th>";

  table.appendChild(headerRow);

  // Program counter, track the current instruction's position
  var pc = block.offset || 0;
  // Simulated stack for tracking values.
  // FIXME: This does not take into account register spilling.
  var virtual_stack = [];

  const color_map = allocate_colors(block.instructions.flatMap(instr => instr.operands).concat(block.instructions.flatMap(instr => instr.outputs)));

  block.instructions.forEach((instr) => {
    if (virtual_stack.length <= instr.operands.length) {
      // Not enough values on the stack, probably the start of the block.
      virtual_stack = []
    } else {
      // Remove operands from stack, then add outputs
      instr.operands.forEach((op) => {virtual_stack.pop();});
    }

    instr.outputs.forEach((out) => {virtual_stack.push(out);});

    const row = document.createElement("tr");
    row.innerHTML = `
      <td>${pc}:</td>
      <td>${format_instruction_name(instr)}</td>
      <td>${virtual_stack.toReversed().map(x => format_operand_locations(color_map, virtual_stack, x)).join(", ")}</td>
      `;
    table.appendChild(row);

    pc += 1;
    if (instr.opcode == 95) {
      // The push instruction is the only variable length instruction
      // The length of the operand is determined by the index
      pc += instr.index;
    }
  });

  // Add terminator
  switch (block.terminator) {
    case "JumpI":
    case "Jump": {

      var dest = "Unknown"
      if (virtual_stack.length == 0) {
        console.error(`Block ${block_id} has no values on stack for jump destination`);
      } else {
        // Add a link to the destination block for jump terminator, if known
        if (virtual_stack[virtual_stack.length - 1].literal !== undefined) {
          const dest_block_id = block_id_at_offset(blocks, parseHex(virtual_stack[virtual_stack.length - 1].literal));
          dest = `<a href="#block-${dest_block_id}">Block #${dest_block_id}</a>`
        }
        // Remove destination
        virtual_stack.pop();
      }

      const row = document.createElement("tr");
      const fall_through_block_id = block.fallthrough_dest;
      row.innerHTML = `
        <td>${pc}:</td>
        <td>${block.terminator.toUpperCase()}</td>
        <td>${dest}</td>
        `;
      table.appendChild(row);
      // Handle JumpI terminator by adding an else instruction
      if (block.terminator == "JumpI") {
        const row = document.createElement("tr");
        row.innerHTML = `
          <td>${pc}:</td>
          <td>ELSE</td>
          <td><a href="#block-${fall_through_block_id}">Block #${fall_through_block_id}</a></td>
          `;
        table.appendChild(row);
      }
      break;
    }
    default: {
      // Other terminators terminate the execution, so no block to link to
      const row = document.createElement("tr");
      row.innerHTML = `
        <td>${pc}:</td>
        <td>${block.terminator.toUpperCase()}</td>
        <td></td>
        `;
      table.appendChild(row);
    }
  }

  blockDiv.appendChild(table);
  return blockDiv;
}
