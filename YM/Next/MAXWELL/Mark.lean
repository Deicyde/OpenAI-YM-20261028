import YM.Next.MAXWELL.Covariance
import YM.Next.MAXWELL.Derives

/-!
# Differential of poly moment

Use an occurrence list throughout. A general read formula used also
with the stress insertion. `positionD`: actual at separated positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open WaveOn Wick
open scoped ContDiff Topology BigOperators

variable {G : Gauge} {j l d m n : ℕ}

def relay (T : Engine G l) (p : Factor G) : Factor G := ⟨p.1+l, T _ p.2⟩

/-- Use the new slot number to synthesize a copy of a bag input. -/
lemma bag_insert {ι : Type*} (Q : ι → Factor G) (v : ι → Fin n) (r : List ι)
    (a : Fin n) (p : Factor G) {x : Points n} (hx : x ∈ conf n) :
    moment G x (update (bag v Q r) a (letter p * bag v Q r a)) =
      pairCost linkEntry (((x a,p) : Limb G) :: r.map fun i => (x (v i), Q i)) := by
  let f : Option ι → Fin n := fun u => u.elim a v
  let g : Option ι → Factor G := fun u => u.elim p Q
  have ht : bag f g (r.map some)=bag v Q r := by simp [funext_iff,bag,List.map_map, Function.comp_def,f,g]
  rw [show update (bag v Q r) a (letter p * bag v Q r a)=bag f g (none :: r.map some) from ?_]
  · rw [bag_rec f g _ hx]; simp [f,g,List.map_map, Function.comp_def]
  funext i; rw [bag_cons,ht]; by_cases h : i=a <;> simp_all [f,g]

private lemma pull_rewire {ι : Type*} (Q : ι → Factor G) (v : ι → Fin n) (r : List ι)
    (a : Fin n) (T : Engine G l) : rewired T (bag v Q r a) = pulls r (fun i u =>
    if a=v i then letter (relay T (Q i))*bag v Q u a else 0) := by
  induction r with
  | nil => rw [pulls_nil]; exact Derivation.map_one_eq_zero _
  | cons i r ih =>
    rw [bag_cons,pulls_cons]; split_ifs with h
    · rw [Derivation.leibniz,ih,show rewired T (letter (Q i)) = _ from (show _ = letter (relay T (Q i)) from rewired_symbol ..)]
      simp only [smul_eq_mul,pulls,Finset.mul_sum]; rw [add_comm, mul_comm (bag v Q r a)]; congr 1
      apply Finset.sum_congr rfl; intro j _; rw [bag_cons,if_pos h]; split_ifs <;> ring
    rw [one_mul,ih,zero_add]; apply pulls_congr; intro j; rw [bag_cons,if_neg h,one_mul]

def beam {ι : Type*} (x : Points n) (v : ι → Fin n) (Q : ι → Factor G) (i : ι) : Limb G := (x (v i),Q i)

def subEdge {ι : Type*} (x : Points n) (v : ι → Fin n) (Q : ι → Factor G) (T : Engine G l) (a : Fin n) (i j : ι) :=
  if a=v i then linkEntry (x a, relay T (Q i)) (beam x v Q j) else 0

def strength {ι : Type*} (x : Points n) (v : ι → Fin n) (Q : ι → Factor G) :=
    fun i j => linkEntry (beam x v Q i) (beam x v Q j)

lemma bag_relay {ι : Type*} (Q : ι → Factor G) (v : ι → Fin n) (r : List ι)
    (a : Fin n) (T : Engine G l) {x : Points n} (hx : x ∈ conf n) :
    moment G x (update (bag v Q r) a (rewired T (bag v Q r a))) = pulls r (fun i R => pulls R (fun j R' =>
      subEdge x v Q T a i j * pairCost (strength x v Q) R')) := by
  rw [pull_rewire, pulls,MultilinearMap.map_update_sum]; unfold pulls
  apply Finset.sum_congr rfl; intro i _; dsimp only
  split_ifs with h
  · rw [show update _ a _ = update (bag v Q (r.eraseIdx i.val)) a
      (letter (relay T (Q _))*bag v Q (r.eraseIdx i.val) a) from ?_, bag_insert _ _ _ a (relay T (Q _)) hx,
      pair_step,pulls_map]
    · unfold pulls; apply Finset.sum_congr rfl; intro b _
      dsimp only; rw [pair_transfer,subEdge,if_pos h]; rfl
    funext k; by_cases he : k=a
    · subst k; rw [update_self,update_self]
    rw [update_of_ne he,update_of_ne he,bag_pick v Q r k i,if_neg (fun hq => he (hq.trans h.symm)),one_mul]
  rw [MultilinearMap.map_coord_zero _ a (update_self ..)];
  simp only [subEdge,h,↓reduceIte,zero_mul, Finset.sum_const_zero]

/-- Differentiate cross-edge cost with oriented edge `u i j`. Symmetric e
on the current points. Stated so orientation can lift to true label
substitution without half factors. -/
private theorem propagate {ι : Type*} (e : ℝ → ι → ι → ℂ) (u : ι → ι → ℂ) (L : List ι)
    (he : ∀ i j, HasDerivAt (fun t => e t i j) (u i j + u j i) 0) :
    HasDerivAt (fun t => pairCost (e t) L) (pulls L fun i r => pulls r fun j s => u i j * pairCost (e 0) s) (0:ℝ) := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | h n ih =>
    subst n; cases L with
    | nil => simp_rw [pairCost,pulls_nil]; exact hasDerivAt_const ..
    | cons a L =>
      let F := pairCost (e 0)
      let R (z) := pulls z fun i r => pulls r fun j s => u i j*F s
      have hd : HasDerivAt (fun t => pulls L fun b p => e t a b * pairCost (e t) p)
          (pulls L fun b p => ((u a b+u b a)*F p + e 0 a b*R p)) (0:ℝ) := by
        unfold pulls; apply HasDerivAt.fun_sum; intro i _
        exact (he a (L.get i)).mul (ih _ (lt_trans (pulls_short i) (by simp)) _ rfl)
      conv => arg 1; ext t; rw [pair_step]
      refine hd.congr_deriv ?_
      have ht : pulls L (fun b p => e 0 a b * R p) = pulls L (fun i r => pulls r
          (fun j s => u i j * pairCost (e 0) (a::s))) := by
        calc
          _ = pulls L (fun b p => pulls p (fun i r => pulls r
            (fun j s => e 0 a b * (u i j * F s)))) := by unfold R pulls; simp_rw [Finset.mul_sum]
          _ = pulls L (fun i p => pulls p (fun b r => pulls r
            (fun j s => e 0 a b * (u i j * F s)))) := pulls_twice L _
          _ = pulls L (fun i p => pulls p (fun j r => pulls r
            (fun b s => e 0 a b * (u i j * F s)))) := by apply pulls_congr; intro i; exact pulls_twice _ _
          _ = _ := by
            simp_rw [pair_step]; unfold F pulls; simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
            apply Finset.sum_congr rfl; intro b _; exact mul_left_comm ..
      simp_rw [pulls_cons]
      unfold pulls at ht ⊢
      simp_rw [add_mul,Finset.sum_add_distrib]
      rw [ht,add_assoc]

private lemma slotD {ι : Type*} (a : Fin n) (v : ι → Fin n) (Q : ι → Factor G)
    {x : Points n} (hx : x ∈ conf _) (b : Axis) (i j : ι) :
    let Y := fun t : ℝ => x+t • Points.direction a b
    let U := subEdge x v Q (glide G (basis b)) a
    HasDerivAt (fun t => strength (Y t) v Q i j) (U i j+U j i) (0:ℝ) := by
  intro Y U
  have hp : Continuous Y := by unfold Y; fun_prop
  have hz : Y 0 = x := by simp [Y]
  have ht (i t) : Y t i = if i=a then x i+t • basis b else x i := by
    by_cases h : i=a <;> simp_all [Y,Points.direction]
  by_cases H : v i=v j
  · have he (Z : Points n) : strength Z v Q i j = 0 := by simp [strength,beam,H,link_zero]
    have hq (i j) (H : v i=v j) : U i j=0 := by
      unfold U subEdge; split_ifs with h
      · simp only [beam,h,H,link_zero]
      rfl
    simp_rw [hq i j H,hq j i H.symm,add_zero, he]; exact hasDerivAt_const ..
  have hv : ∀ᶠ t : ℝ in 𝓝 0, Y t ∈ conf n := hp.continuousAt.preimage_mem_nhds
    ((conf_open _).mem_nhds (show Y 0 ∈ conf n from hz.symm ▸ hx))
  have he : (fun t => strength (Y t) v Q i j) =ᶠ[𝓝 0] fun t =>
      ((K (Q i).2 (Q j).2 (Y t (v i)) (Y t (v j)) : ℝ) : ℂ) := by
    filter_upwards [hv] with t ht
    exact link_eq _ _ _ _ ((show Injective (Y t).ofLp from ht).ne H)
  apply HasDerivAt.congr_of_eventuallyEq (f := fun t => _) _ he
  have hs (u : E4) : HasDerivAt (fun t : ℝ => u+t • basis b) (basis b) 0 := by
    apply HasDerivAt.congr_deriv (((hasDerivAt_id' (0:ℝ)).smul_const (basis b)).const_add u); simp
  have hc {d l : ℕ} (p : Probe G d) (q : Probe G l) (y z : E4) (h : y≠z) :
      HasDerivAt (fun t : ℝ => ((K p q (y+t • basis b) z : ℝ):ℂ))
        ((K (raiseLeg (basis b) p) q y z:ℝ):ℂ) 0 := by
    let D : E4 → ℝ := fun x => K p q x z
    have hq : y+(0:ℝ) • basis b ≠ z := by simpa using h
    have ht : DifferentiableAt ℝ D (y+(0:ℝ) • basis b) :=
      ((K_smooth p q (y+(0:ℝ) • basis b,z) hq).comp _ (f := fun x => (x,z))
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    have hm := ht.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hs y)
    refine Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hm.congr_deriv ?_)
    simp only [zero_smul, add_zero]
    exact K_left_D p q h _
  have hd : x (v i) ≠ x (v j) := (show Injective x.ofLp from hx).ne H
  unfold U subEdge
  by_cases h : a=v i
  · have hw : a≠v j := fun he => H (h.symm.trans he)
    rw [if_pos h, if_neg hw,add_zero]
    unfold beam; rw [show x a=x (v i) from congr_arg x.ofLp h, link_eq _ _ _ _ hd]
    simp_rw [ht, if_pos h.symm, if_neg hw.symm]
    exact hc _ _ _ _ hd
  rw [if_neg h,zero_add]; by_cases h' : a=v j
  · rw [if_pos h']; unfold beam; rw [show x a=x (v j) from congr_arg x.ofLp h',link_eq _ _ _ _ hd.symm]
    apply (hc (Q j).2 (Q i).2 (x (v j)) (x (v i)) hd.symm).congr_of_eventuallyEq
    filter_upwards [hv] with t ht'
    rw [K_symmetric _ _ ((show Injective (Y t).ofLp from ht').ne H)]
    rw [ht, ht (v i) t]; simp only [if_pos h'.symm, if_neg (Ne.symm h)]
  simp_rw [if_neg h',ht, if_neg (show v i ≠ a from Ne.symm h), if_neg (show v j ≠ a from Ne.symm h')]; exact hasDerivAt_const ..

lemma change_slot {ι : Type*} (a : Fin n) (v : ι → Fin n) (Q : ι → Factor G) {x : Points n} (hx : x ∈ conf _)
    (p : List ι) (b : Axis) : Points.gradient a b (fun z => moment G z (bag v Q p)) x =
      moment G x (update (bag v Q p) a (rewired (glide G (basis b)) (bag v Q p a))) := by
  let Y := fun t : ℝ => x+t • Points.direction a b
  have he : Y 0=x := by simp [Y]
  have ht : HasDerivAt Y (Points.direction a b) 0 := by
    apply HasDerivAt.congr_deriv (((hasDerivAt_id' (0:ℝ)).smul_const (Points.direction a b)).const_add x); simp
  have h := propagate (fun t : ℝ => strength (Y t) v Q) (subEdge x v Q (glide G (basis b)) a) p (slotD a v Q hx b)
  have hg := ((moment_smooth (bag v Q p) (show Y 0 ∈ conf _ from he.symm ▸ hx)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ht
  simp only [he] at hg h
  rw [bag_relay _ _ p _ _ hx]
  apply hg.unique (h.congr_of_eventuallyEq ?_)
  have hy := (ht.continuousAt).tendsto
  filter_upwards [hy ((conf_open _).mem_nhds (show Y 0 ∈ conf _ from he.symm ▸ hx))] with t ht
  change moment G (Y t) _ = _; rw [bag_rec v Q p ht,pair_transfer]; rfl

lemma substitution (x : Points n) (i : Fin n) (L : Module.End ℂ (WickPol G)) :
    ∃ A : MultilinearMap ℂ (fun _ : Fin n => WickPol G) ℂ, ∀ v,
      A v=moment G x (update v i (L (v i))) := by
  let A := (moment G x).compLinearMap (fun j => if i=j then L else LinearMap.id)
  refine ⟨A,fun v => ?_⟩
  simp only [A,MultilinearMap.compLinearMap_apply]; congr 1
  ext1 j; by_cases h : i=j <;> simp_all
  simp [Function.update,Ne.symm h]

lemma positionD (v : Fin n → WickPol G) {x : Points n} (hx : x ∈ conf _) (a : Fin n) (b : Axis) :
    Points.gradient a b (fun z => moment G z v) x =
      moment G x (update v a (rewired (glide G (basis b)) (v a))) := by
  classical
  obtain ⟨L,hL⟩ := substitution x a (rewired (glide G (basis b))).toLinearMap
  rw [show moment G x (update v a (rewired (glide G (basis b)) (v a))) = L v from (hL _).symm,
    Multilabel.expansion (fun _ => monBasis G) L]
  simp_rw [sumFormula]; unfold Points.gradient D
  let f := fun e : Powers G n => fun z : Points n => monomial z e
  have hs (e) : DifferentiableAt ℝ (f e) x := (monomial_smooth e hx).differentiableAt (by simp)
  let c (e : Powers G n) := ∏ i, (monBasis G).repr (v i) (e i)
  rw [fderiv_fun_sum]
  · rw [_root_.sum_apply]
    apply Finset.sum_congr rfl; intro e _
    change fderiv ℝ (fun z => c e * f e z) x _ = _
    rw [fderiv_const_mul (hs e)];
    change c e * Points.gradient a b (f e) x = _
    congr 1
    obtain ⟨p,hp⟩ := power_bag e
    rw [show f e = fun y => moment G y (bag Prod.fst Prod.snd p) by ext1; rw [hp,moment_basis],change_slot _ _ _ hx p]
    exact hp ▸ (hL _).symm
  intro e _; exact (hs e).const_mul _
end YM.Maxwell.Free
