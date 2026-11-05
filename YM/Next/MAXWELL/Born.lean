import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.Next.MAXWELL.Canopy
import YM.Next.MAXWELL.System
import YM.Pressure.Seeds


/-! # True nonzero derivative (weight four threshold) -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open Climb
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G : Gauge}

lemma has_sheet (h : G.Simple) (j : ℕ) : Nontrivial (Sheet j) := by
  by_contra ht
  haveI : Subsingleton (Sheet j) := not_nontrivial_iff_subsingleton.mp ht
  refine cell_alive (ranging (coreColor h) (cell 0 1) j ?_)
  intro z hz q; rw [← fare_pair (coreColor h) _ _ hz, Subsingleton.elim q 0, map_zero]

private lemma provide (h : G.Simple) : ∃ (p : Flavor 0) (a : Axis), feed (basis a) 0 p ≠ 0 := by
  letI := has_sheet h 1
  obtain ⟨x,hx⟩ := exists_ne (0:Sheet 1)
  by_contra! H
  apply hx
  apply flavor_ext; intro u a b; rw [map_zero]
  let F := x.val a b
  have ht (i : Axis) : feed (basis i) 0 (cell a b) x=0 := by rw [H]; rfl
  have he (i) : F (fun _ => basis i)=0 := by
    have hp := ht i
    change (↑(0+1 : ℕ):ℝ) • F (Fin.cons (basis i) _) = 0 at hp
    rw [Nat.zero_add,Nat.cast_one,one_smul] at hp
    refine Eq.trans ?_ hp
    congr 1; funext j; fin_cases j; rfl
  have hf (v) : F (fun _ => v)=0 := by
    let V := ((F.curryLeft) : E4 →L[ℝ] Tensor.T E4 ℝ 0)
    have hk i : V (basis i)=0 := by
      ext1 u; refine Eq.trans ?_ (he i)
      change F _=F _; congr 1; funext j; fin_cases j; rfl
    rw [show v = ∑ i : Axis, v i • basis i by ext1; simp]
    let z := ∑ i : Axis, v i • basis i
    rw [show (fun _ : Fin 1 => ∑ i : Axis, v i • basis i) = Fin.cons (α:=fun _ => E4) z (fun _ : Fin 0 => 0) by
      ext1 i; fin_cases i; rfl]
    change V (∑ i : Axis, v i • basis i) (fun _ => 0) = 0
    simp only [map_sum,map_smul,hk,smul_zero,Finset.sum_const_zero]; rfl
  change F u = _
  rw [show u=fun _ => u 0 by funext i; fin_cases i; rfl,hf]

lemma born (h : G.Simple) (F : Labels.Frames G) {d : ℕ} (hd : 4 ≤ d) : leaves (scheme F).deriv d≠0 := by
  obtain ⟨p,b,hp⟩ := provide h
  let q := feed (basis b) 0 p
  have hn : p ≠ 0 := by intro he; rw [he,map_zero] at hp; contradiction
  have hv : team G p q ≠ 0 := by
    intro H
    have ht : monoT p q=0 := canopy_faithful (coreColor h) (by decide) (by rw [shelter,H,map_zero])
    apply hn
    apply LinearMap.ext; intro x
    have he : p x • q=0 := LinearMap.congr_fun ht x
    exact (smul_eq_zero.mp he).resolve_right hp
  let B := team G p p
  let Q := (fields F d).symm ⟨B,team_label p p hd⟩
  have hx : address F d Q = B := by rw [address_eval,show fields F d Q=_ from (fields F d).apply_symm_apply _]
  intro hw
  have he : (scheme F).deriv d b Q=0 := congr_arg (fun f : Climb.Vector d (Model F) => f b Q) hw
  have hm : (2:ℝ) • team G p q=0 := calc
    (2:ℝ) • team G p q = address F _ ((scheme F).deriv d b Q) := by rw [address_derive,hx,team_feed]
    _ = 0 := by rw [he,map_zero]
  exact hv ((smul_eq_zero.mp hm).resolve_left (by norm_num))
end YM.Maxwell.Free
