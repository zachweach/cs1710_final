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

// test expects for partial instances
test expect {
  // this one is a fully complete instance, testing that traces works for a situation that we know to be valid
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

  worldOneBasic: {
    traces
    some disj hill, monster, target, trader, island, gifter: Chest, ladder, boat, sword, bow, emerald: Item | {
      #Chest = 6
      #Item = 5

      hill.prereqs = ladder
      trader.prereqs = emerald
      no gifter.prereqs
      island.prereqs = boat
      target.prereqs = bow
      monster.prereqs = sword
    }
  } for 6 Chest, 5 Item is sat

  worldOnePossible: {
    traces
    some disj hill, monster, target, trader, island, gifter: Chest, ladder, boat, sword, bow, emerald: Item | {
      #Chest = 6
      #Item = 5

      hill.prereqs = ladder
      trader.prereqs = emerald
      no gifter.prereqs
      island.prereqs = boat
      target.prereqs = bow
      monster.prereqs = sword

      hill.contains = bow
      trader.contains = ladder
      gifter.contains = emerald
      no island.contains
      target.contains = sword
      monster.contains = boat
    }
  } for 6 Chest, 5 Item is sat

  worldOneCannotOpenAny: {
    traces
    some disj hill, monster, target, trader, island, gifter: Chest, ladder, boat, sword, bow, emerald: Item | {
      #Chest = 6
      #Item = 5

      hill.prereqs = ladder
      trader.prereqs = emerald
      no gifter.prereqs
      island.prereqs = boat
      target.prereqs = bow
      monster.prereqs = sword

      hill.contains = bow
      trader.contains = ladder
      no gifter.contains
      island.contains = emerald
      target.contains = sword
      monster.contains = boat
    }
  } for 6 Chest, 5 Item is unsat

  worldOneChestContainsPrereq: {
    traces
    some disj hill, monster, target, trader, island, gifter: Chest, ladder, boat, sword, bow, emerald: Item | {
      #Chest = 6
      #Item = 5

      hill.prereqs = ladder
      trader.prereqs = emerald
      no gifter.prereqs
      island.prereqs = boat
      target.prereqs = bow
      monster.prereqs = sword

      hill.contains = ladder
      trader.contains = bow
      gifter.contains = emerald
      no island.contains 
      target.contains = sword
      monster.contains = boat
    }
  } for 6 Chest, 5 Item is unsat

  // the first dungeon from The Legend of Zelda
  // We originally planned to test a larger instance of a game. Below you will see the test we wrote
  // for this instance. Unfortunately, we waited for over an hour for the first test to run with no
  // conclusion. Due to this long and uncertain runtime, we have decided to comment these tests out while
  // leaving them in to show our efforts in extensively testing the project.
  // theEagleVanilla: {
  //   traces
  //   some bow, boomerang, triforce, map, compass, keeseKey, stalKey1, stalKey2, stalKey3, goriyaKey, wallKey: Item,
  //   RM1, RM2, RM3, RM4, RM5, RM6, RM7, RM8, RM9, RM10, RM11: Chest | {
  //     #Chest = 11
  //     #Item = 11

  //     no RM1.prereqs
  //     no RM2.prereqs
  //     RM3.prereqs = keeseKey 
  //     RM4.prereqs = keeseKey
  //     RM5.prereqs = keeseKey + stalKey1
  //     RM6.prereqs = keeseKey + stalKey1
  //     RM7.prereqs = keeseKey + stalKey1 + stalKey2
  //     RM8.prereqs = keeseKey + stalKey1 + stalKey2 + goriyaKey
  //     RM9.prereqs = keeseKey + stalKey1 + stalKey3
  //     RM10.prereqs = keeseKey + stalKey1 + stalKey3
  //     RM11.prereqs = keeseKey + stalKey1 + stalKey3 + wallKey + bow + boomerang

  //     RM1.contains = keeseKey
  //     RM2.contains = stalKey1
  //     RM3.contains = stalKey2 
  //     RM4.contains = compass
  //     RM5.contains = map
  //     RM6.contains = stalKey3
  //     RM7.contains = goriyaKey
  //     RM8.contains = bow
  //     RM9.contains = boomerang
  //     RM10.contains = wallKey
  //     RM11.contains = triforce
  //   }
  // } for 11 Chest, 11 Item is sat

  // theEagleMissingFirstItem: {
  //   traces
  //   some disj bow, boomerang, triforce, map, compass, keeseKey, stalKey1, stalKey2, stalKey3, goriyaKey, wallKey: Item,
  //   RM1, RM2, RM3, RM4, RM5, RM6, RM7, RM8, RM9, RM10, RM11: Chest | {
  //     #Chest = 11
  //     #Item = 11

  //     no RM1.prereqs
  //     no RM2.prereqs
  //     RM3.prereqs = keeseKey 
  //     RM4.prereqs = keeseKey
  //     RM5.prereqs = keeseKey + stalKey1
  //     RM6.prereqs = keeseKey + stalKey1
  //     RM7.prereqs = keeseKey + stalKey1 + stalKey2
  //     RM8.prereqs = keeseKey + stalKey1 + stalKey2 + goriyaKey
  //     RM9.prereqs = keeseKey + stalKey1 + stalKey2 + goriyaKey + stalKey3
  //     RM10.prereqs = keeseKey + stalKey1 + stalKey2 + goriyaKey + stalKey3
  //     RM11.prereqs = keeseKey + stalKey1 + stalKey2 + goriyaKey + stalKey3 + wallKey + bow + boomerang

  //     RM1.contains = triforce
  //     RM2.contains = compass
  //   }
  // } for 11 Chest, 11 Item is unsat
}

pred wellformed {
  // firstChest is actually the first chest in the chain
  no next.(Player.firstChest)

  all c: next.Chest + Chest.next | c in Player.firstChest.*next

  // there is at most one ending chest (the last opened chest)
  lone last: Chest | (some next.last) and (no last.next)

  // no cycles
  all c: Chest | c not in c.^next
}

pred goodTransition {
  // contains and prereqs do not change
  contains = contains'
  prereqs = prereqs'

  // bag is only addative
  Player.bag in Player.bag'
}

// induction: opening cannot put us in a "bad" state
test expect {
  base: {
    init and not wellformed
  } is unsat

  inductiveStep: {
    wellformed
    some c: Chest | opening[c]
    next_state not wellformed
  } is unsat

  openingAlwaysGood: {
    (some c: Chest | opening[c]) implies (goodTransition)
  } is theorem
}
