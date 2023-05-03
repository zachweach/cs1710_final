#lang forge

option problem_type temporal 
option max_tracelength 10

-- IDEA: option for consumable items (they disappear from bag when used)
sig Item {}

sig Chest {
  contains: lone Item,
  prereqs: set Item,
  var next: lone Chest
}

// IDEA: multiplayer games?
one sig Player {
  var firstChest: lone Chest,
  var bag: set Item
}

// chest opening pattern (solution) is linear
pred chestsLinear {
  // there exists one chest that doesn't have a next
  one c: Chest | no c.next 
  one c: Chest | {
    // there exists one chest that doesn't have a previous
    no next.c 

    // all chests are reachable from the first chest
    all other: Chest | other in c.*next
  }
  { some Player.firstChest } or { no Chest } -- there is a first chest or there are no chests at all
}

pred init {
  // no chests have been opened
  no Chest.next
  no Player.firstChest
  
  // Player's bag is empty
  no Player.bag
}

// what is required for a chest to be opened
pred opening[c: Chest] {
  // GAURD
  // it hasn't been opened yet
  no next.c

  // Player has the prereqs
  c.prereqs in Player.bag -- the prereqs are in the player's bag

  // TRANSITION
  // the next field is set appropriately
  some prev: Chest | {
    some next.prev -- exists in the chain of chests that have been opened
    no prev.next   -- is at the end of the chain of chests that have been opened

    prev.next' = c -- the last thing we opened is now the current chest

    no Player.firstChest implies Player.firstChest' = c -- if there isn't a first chest, then the next chest to be opened will be the first one
    
    // all other chests stay the same
    all other: Chest | {  
      other != prev
      other.next' = other.next
    }
  }

  // the current items of the chest are added to the player's bag
  Player.bag' = Player.bag + c.contains
}

// all chests are opened, so we reset to init state
pred reset {
  // GAUARD
  chestsLinear

  // TRANSIION
  next_state init
}

pred traces {
  // there is some initial state
  init

  // we are always opening a chest or resetting (finished)
  always { 
    reset
    or 
    { some c: Chest | opening[c] }
  }
}

run {
  -- we only make valid moves
  { some c: Chest | opening[c] }
} //for exactly 5 Chest

// test expect {
//   solutionExists: {
//     some c1, c2, c3, c4, c5: Chest, sword, shield, key, arrows, bow: Item | {
//       -- Make sure the chests and items are enumerated
//       #Chest = 5
//       #Item = 5

//       -- define chest contents
//       c1.contains = shield
//       c2.contains = key
//       c3.contains = arrows
//       c4.contains = sword
//       c5.contains = bow

//       -- define prereqs
//       c1.prereqs = key + sword
//       no c2.prereqs
//       c3.prereqs = key
//       c4.prereqs = key
//       c5.prereqs = shield
//     }
//   } is sat
// }