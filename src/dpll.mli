open Solver


 (** DPLL is a SAT solver parameterized by a choice function. *)
module DPLL(C:CHOICE) : SOLVER

(** Implement a choice by Default. More choices can be implemented. *)
module DefaultChoice : CHOICE
