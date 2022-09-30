# Code for my MScThesis

This repository serves to keep the code I did for my thesis, titled "Homotopy Type Theory: a Comprehensive Survey", easily accessible for reference.

I'll have two folders: one will hold the version I had the day I submitted my thesis (without any change); the other will have improved code, done after the submission.

The version submitted in 30/9/2022 has the following files:

### Types.agda
This file implements the basic types needed, which corresponds roughly to Chapter 2.

### Univalence.agda
This file implements the notions needed for the Univalence Axiom, as well as the axiom itself, which corresponds roughly to Chapter 3.2.

### Interval.agda, Circle.agda, Other_Circle.agda
Circle.agda implements the Circle using HITs, which corresponds to Chapter 3.1; Interval.agda does the same for the unit interval, which isn't talked about in the thesis. Other_Circle.agda has the some other implementations used as example.

### SeqViews.agda
This file corresponds to the implementations of Chapter 4, which treats Views and the HoTT solution to the problem at https://homotopytypetheory.org/2012/11/12/abstract-types-with-isomorphic-types/, from where it translates some code and finishes some uncompleted things.
It also has some proofs not presented in the thesis.


### EqReasoning.agda
This file implements some auxiliary devices to prove statements. The most relevant things are symmetry and transitivity, from the end of Chapter 2.4.

### Playground.agda
A non-essential file which I used to try (sometimes very silly) stuff.
