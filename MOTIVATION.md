# Motivation

There is almost no doubt in many parts of the math community that agents can do math better than humans. Mathematical optimization no exception. The current agents are very good and fast at generating proofs in mathematical optimization. Nevertheless, (for now) the agents still have to be guided and controlled by humans to investigate the right question and research direction.

Having this in mind, we developed the LongTails framework. The user defines a **Setup**, a problem where the user wants to develop an efficient algorithm and prove its theoretical convergence. The philosophy of the framework is that all other steps (deriving algorithms, proofs, and final derivations of **Complexities**) should be handled by agents.

Of course, we want to be sure that the **Complexity** is correct for the given **Setup**. The framework is built in Lean 4 to make sure that it is indeed true. We designed a particular abstraction in [Template.lean](LongTails/Template.lean) to make sure the agent solves what we want.
