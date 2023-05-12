# RPG Randomizer
## What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

Initially, our model did not use temporal mode, since we sought to model the complete instance without a sense of time. While implementing the model, however, we realized that the process of opening chests and adding items to our bag behaved similarly to a time-based system, so we switched to using temporal mode part-way through. Before this switch, we also considered using a `pfunc` to describe the “next chest” sequence instead of the `var next` field we have now. Lastly, we added a `firstChest` field to the `Player` sig, since we found it necessary to mark the first chest that we would open. Doing this allowed us to represent the first chest being opened (since it would not have any next relation). Additionally, it allowed us to write other constraints more easily by having a reference to the first chest in the chain.  

## What assumptions did you make about scope? What are the limits of your model?

We made several modeling decisions to narrow the scope of the project that selected only the most important attributes of the system we are trying to model. First, we have no way of representing items that are consumable. For example, you might have a key that disappears after use in opening a chest. In our model, the key will remain in the player’s inventory forever. Second, items found in chests have to be unique. This connects to consumables — if I have a bundle of arrows that can be found in multiple chests, this would have to be represented as discrete `Item`s instead of the same item that can be found in multiple chests. Next, `Item`s can only be found when opening chests. Many RPGs allow items or currency to be found on the ground or via quests, but our model only accounts for items being found in chests. In a way, you could consider items on the ground to be in a chest with no `prereq`s and items obtained via quests to be “in a chest” (with the chest being the reward for the quest). Last, you cannot have a system with no chests. This is not a particularly interesting situation, but regardless our model cannot represent this system, since `chestsLinear` (which determines that the setup is playable) assumes at least one chest exists. 

## Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

We added a new reach goal for items that are consumable. For example, a key might only be able to be used once, but our model keeps it forever. To change this, the player’s `bag` would have to be made not only additive, but also subtracted from when an item is used. We did not implement this reach goal, but future work on this project might include implementing this system.

## How should we understand an instance of your model and what your custom visualization shows?

Each “chest” in the model represents a possibility of obtaining an item, such as opening a reward chest or completing an in-game quest. At the start of the game (the initial state), all of the chests have been filled with the random items and the instance is “possible to beat” if all chests can be opened.

As time progresses, the player opens chests, which saves the record of the order that the chests were opened (in `firstChest` and `next`) and also the items that the player has obtained so far (`bag`). The game is considered “won” when every chest has been opened. When this occurs, we reset back to the initial state for the lasso, which would be the equivalent of restarting the game with the same randomized item locations.

Video link: https://drive.google.com/file/d/11zyePuJrFzGUcg5CuDYcp-1IU-U9x963/view?usp=sharing
