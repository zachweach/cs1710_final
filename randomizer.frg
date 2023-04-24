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

one sig Player {
  var bag: set Item
  // chest ordering here? pfunc?
}

// chest opening pattern (solution) is linear
pred chestsLinear {
  one c: Chest | no c.next -- there exists one chest that doesn't have a next
  one c: Chest | {
    no next.c -- there exists one chest that doesn't have a previous
    all other: Chest | other in c.*next -- all chests are reachable from the first chest
  }
}

pred init {
  -- no chests have been opened
  -- Player's bag is empty
}

// what is required for a chest to be opened
pred open[c: Chest] {
  -- it hasn't been opened yet
  -- the next field is set appropriately
  -- Player has the prereqs
  -- Player's bag is updated appropriately
}

pred doNothing {
  -- vars dont change
}

pred traces {
  -- there is some initial state
  -- we are always opening a chest or doing nothing
}

run {
  -- we eventually find a solution
  // eventually chestsLinear
  -- we only make valid moves
  // traces
}

test expect {
  solutionExists: {
    some c1, c2, c3, c4, c5: Chest, sword, shield, key, arrows, bow: Item | {
      -- Make sure the chests and items are enumerated
      #Chest = 5
      #Item = 5

      -- define chest contents
      c1.contains = shield
      c2.contains = key
      c3.contains = arrows
      c4.contains = sword
      c5.contains = bow

      -- define prereqs
      c1.prereqs = key + sword
      no c2.prereqs
      c3.prereqs = key
      c4.prereqs = key
      c5.prereqs = shield
    }
  } is sat
}