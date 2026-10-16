(*
GallinaC: Unifying Verification and Certified Compilation of System Programs in Rocq
Copyright (C) 2023-2026 GallinaC contributors (see CONTRIBUTORS.md)

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
*)

From GallinaC Require Export Programming.
From GallinaC.Seplog Require Export Pred.
From GallinaC.Seplog.Inter Require Export Inter Facts.
From GallinaC.Seplog.Exists Require Export Exists Facts.
From GallinaC.Seplog.Union Require Export Union Facts.
From GallinaC.Seplog.Forall Require Export Forall Facts.
From GallinaC.Seplog.Emp Require Export Emp.
From GallinaC.Seplog.Stateless Require Export Stateless.
From GallinaC.Seplog.Lift Require Export Lift Facts.
From GallinaC.Seplog.Precise Require Export Precise Facts.
From GallinaC.Seplog.Star Require Export Star Facts.
From GallinaC.Seplog.Intuitionistic Require Export Intuitionistic.
From GallinaC.Seplog.Upclose Require Export Upclose Facts.
From GallinaC.Seplog.Wand Require Export Wand Facts.
From GallinaC.Seplog.Septract Require Export Septract Facts.
From GallinaC.Seplog.Carve Require Export Carve Facts.
From GallinaC.Seplog.IterStar Require Export IterStar Facts.
From GallinaC.Seplog.ConjOverlap Require Export ConjOverlap Facts.
From GallinaC.Seplog.State Require Export EmpHeap.
From GallinaC.Seplog.Indep Require Export Indep.
From GallinaC.Seplog.ConjOverlapStore Require Export ConjOverlapStore Facts.
From GallinaC.Seplog.Indep Require Export Facts.
From GallinaC.Seplog.State Require Export Atoms.
From GallinaC.Seplog Require Export ListAssertion Frame.
From GallinaC.Seplog.Inter Require Export Frame.
From GallinaC.Seplog.Star Require Export Frame.
From GallinaC.Seplog Require Export Ramify.
From GallinaC.Seplog.ConjOverlap Require Export Frame.
From GallinaC.Seplog.ConjOverlapStore Require Export Frame.
From GallinaC.Seplog Require Export GenTriples PrimitivesTriples Hoare.
From GallinaC.Seplog.Union Require Export Union.

Open Scope separation_scope.
