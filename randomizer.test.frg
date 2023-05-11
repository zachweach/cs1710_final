#lang forge

open "randomizer.frg"

// test expects for all preds

// chestsLinear
test expect {
    
  // chestsLinear is possible
  vacuity: {chestsLinear} is sat
  // there exists one chest that does not have a next
  oneWithoutNext: {
    chestsLinear implies (one c: Chest | no c.next)
  } is theorem
  // there exists one chest that does not have a previous
  oneWithoutPrev: {
    chestsLinear implies (one c: Chest | no next.c)
  } is theorem
  // all chests are reachable from firstChest
  firstChestReachesAll: {
    chestsLinear implies (all c: Chest | c in Player.firstChest.*next)
  } is theorem
  // chests don't produce a cycle
  noCycles: {
    chestsLinear implies (no c: Chest | c in c.^next)
  } is theorem
}

// init
test expect {
  // it's possible to have an initial state
  vacuity: {init} is sat

  // none of the chests have been opened yet
  noOpenChests: {
    init implies (no next and no firstChest)
  } is theorem

  // all chests have a unique item and all items are in a chest
  itemsUnique: {
    init implies (#Item = #contains)
  } is theorem
}

// opening
test expect {
  // opening is possible
  canHaveChests: {#Chest > 0} is sat
  vacuity: {#Chest > 0 implies (some c: Chest | opening[c])} is sat
  // the player has the prereqs in their bag to open the chest
  hasPrereqs: {
    #Chest > 0 implies { some c: Chest | {
      opening[c] implies (c.prereqs in Player.bag)
    } }
  } is theorem
  // only one chest is being opened at a time
  openOnlyOneChest: {
    #Chest > 0 implies { some c: Chest | {
      opening[c] implies {
        all other: Chest | (other != c) implies (not opening[other])
      }
    } }
  } is theorem
}

// traces
test expect {
  // traces is possible
  vacuity: {traces} is sat
  // there is an initial state
  canBeInit: {traces implies init} is theorem
  // the trace will always eventually loop back to the initial state
  loopToInit: {
    traces implies (always (eventually init))
  } is theorem
  // a solution will always be found
  alwaysSolution: {
    traces implies eventually chestsLinear
  } is theorem
}

// minimal examples, incl the one in our doc
test expect {
  designProposal: {
    traces
    some disj c1, c2, c3, c4, c5: Chest, sword, shield, arrows, key, bow: Item | {
      // Make sure the chests and items are enumerated
      #Chest = 5
      #Item = 5

      // define chest contents
      c1.contains = shield 
      c2.contains = key    
      c3.contains = arrows 
      c4.contains = sword  
      c5.contains = bow    

      // define prereqs
      c1.prereqs = key + sword
      no c2.prereqs
      c3.prereqs = key
      c4.prereqs = key
      c5.prereqs = shield

      // this chain of opening chests is valid
      Player.firstChest' = c2
      c2.next'' = c3
      c3.next''' = c4
      c4.next'''' = c1
      c1.next''''' = c5

      // each item should be added to the bad
      no Player.bag
      Player.bag' = key
      Player.bag'' = key + arrows
      Player.bag''' = key + arrows + sword
      Player.bag'''' = key + arrows + sword + shield
      Player.bag''''' = key + arrows + sword + shield + bow
    }
  } for 5 Chest, 5 Item is sat
}

// test expects for partial instances

// firstChest antics
// - firstChest is always the first (induction?)

// induction: opening cannot put us in a "bad" state