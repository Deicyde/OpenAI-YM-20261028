import YM.Bid.Loan
import YM.Bid.Station
import YM.Next.MAXWELL.System
import YM.Next.MAXWELL.Taxes

/-!
# Framework for the finite-weight Ward tests

At capacity d: ALL spectator words built from that cap. Don't confuse
this with the all-spectator tests in residual. Include the central
commutator identity from the normalized (or non-normalized) flux, before
returning to a detecting family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder

variable {G : Gauge} {d k m n : ℕ}

def wrap (F : Labels.Frames G) {d : ℕ} {p : WickPol G} (h : p∈shellSector G d) : (Model F).Field d :=
    (fields F d).symm ⟨p,h⟩
@[simp] theorem shed (F : Labels.Frames G) {p : WickPol G} (h : p∈shellSector G d) :
    address F d (wrap F h)=p := by rw [address_eval]; unfold wrap; rw [LinearEquiv.apply_symm_apply]

def brand (F : Labels.Frames G) {d e : ℕ} (W : (Model F).Field d →ₗ[ℂ] (Model F).Field e) : Module.End ℂ (WickPol G) :=
    (address F e).comp (W.comp (address F d).leftInverse)

lemma brand_eval (F : Labels.Frames G) {d e : ℕ} (W : (Model F).Field d →ₗ[ℂ] (Model F).Field e)
    (x : (Model F).Field d) : brand F W (address F d x) = address F e (W x) := by
  unfold brand; rw [LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (address_inj F d))]

lemma brand_fit (F : Labels.Frames G) {d e : ℕ} (W : (Model F).Field d →ₗ[ℂ] (Model F).Field e)
    (x : WickPol G) : brand F W x∈shellSector G e := address_in F _ _

/-- E sum. Polys are off quotient notation, T allowed on all with the
bound kept here. -/
def silence (G : Gauge) (d : ℕ) (T : Module.End ℂ (WickPol G)) : Prop :=
    ∀ (n : ℕ) (v : Fin n→ WickPol G) (x : Points n), (∀ i,v i∈shellSector G d) → x∈conf _ →
      (∑ i, moment G x (update v i (T (v i))))=0

lemma own (F : Labels.Frames G) {d e} (W : (Model F).Field d →ₗ[ℂ] (Model F).Field e) (u : Fin n → (Model F).Field d)
    (x : Points n) (i : Fin n) : Ward.disc (update (Climb.column u) i (⟨_,W (u i)⟩ : (Model F).Tag)) x =
      moment G x (update (address F d ∘ u) i (brand F W (address F d (u i)))) := by
  unfold Ward.disc
  rw [display,brand_eval]; congr 1
  ext1 j; by_cases h : j=i
  · subst j; simp only [comp_apply,update_self]; rfl
  simp only [comp_apply,Function.update_of_ne h]; rfl

lemma branded (F : Labels.Frames G) {d e} (W : (Model F).Field d →ₗ[ℂ] (Model F).Field e) :
    (∀ n (u : Fin n → (Model F).Field d) (x : Points n), x∈conf _ →
    (∑ i, Ward.disc (update (Climb.column u) i (⟨_,W (u i)⟩ : (Model F).Tag)) x)=0) ↔ silence G d (brand F W) := by
  constructor
  · intro H n v x hv hx
    let u := fun i => wrap F (hv i)
    have h := H n u x hx; simp_rw [own F W u x, u, shed] at h
    rw [show (address F d ∘ fun i ↦ wrap F (hv i))=v from funext fun i => shed F (hv i)] at h
    exact h
  intro H n u x hx; simp_rw [own F W u x]; exact H n _ x (fun i => address_in F _ (u i)) hx

/-- The testing subspace at a finite exterior weight bound. -/
def ghost (G : Gauge) (d : ℕ) : Submodule ℂ (WickPol G) where
  carrier := {p| ∀ (n : ℕ) (v : Fin n → WickPol G) (x : Points (n+1)), (∀ i,v i∈shellSector G d) → x∈conf _ →
    moment G x (Fin.cons p v)=0}
  zero_mem' n v x _ _ := (moment G x).map_coord_zero 0 (Fin.cons_zero ..)
  add_mem' {p q} H K n v x hv hx := by
    let U z := Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) z v
    change moment G x (U (p+q))=0
    rw [show U (p+q) = update (U p) 0 (p+q) from (Fin.update_cons_zero ..).symm, MultilinearMap.map_update_add]
    unfold U; rw [Fin.update_cons_zero, Fin.update_cons_zero, H n v x hv hx,K n v x hv hx,add_zero]
  smul_mem' c p H n v x hv hx := by
    rw [show Fin.cons (c • p) v=update (Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) p v) 0 (c • p) from
      (Fin.update_cons_zero ..).symm, MultilinearMap.map_update_smul, Fin.update_cons_zero,H n v x hv hx,smul_zero]

lemma ghost_le (h : d≤m) : ghost G m ≤ ghost G d := fun _ H n v x hv hx => H n v x (fun i => chain h (hv i)) hx

lemma ghosts_out {p : WickPol G} (hp : p∈shellSector G d) (h : p∈ghost G d) : p=0 := by
  by_contra H
  let t := points (fun _ : Fin 1 => basis timeAxis)
  have hx : Table.Pairing.single t timeAxis := ⟨injective_of_subsingleton _,fun _ => by simp [t,Axis]⟩
  have he := detects timeAxis (basis timeAxis) (by simp) p H
  let s := Table.Pairing.closedUp timeAxis t t
  let q := mirrorBar (Signed.reflect timeAxis) p
  let r := Equiv.swap (0 : Fin 2) 1
  have hv := Table.Pairing.spans hx hx
  change 0 < moment G s (Fin.append (fun _ => q) (fun _ => p)) at he
  rw [exchangeSites r hv] at he
  have heq : (Fin.append (fun _ : Fin 1 => q) (fun _ : Fin 1 => p) ∘ r)=Fin.cons p (fun _ => q) := by
    ext1 i; fin_cases i <;> simp [r] <;> rfl
  rw [heq] at he
  change 0 < (moment G (Points.rearrange r (Table.Pairing.closedUp timeAxis t t))) (Fin.cons p fun _ => q) at he
  rw [show moment G _ (Fin.cons (α:=fun _ : Fin 2 => WickPol G) p (fun _ => q))=0 from
    h 1 _ _ (fun _ => ?_) (Points.rearrange_in r hv)] at he
  · exact lt_irrefl _ he
  obtain ⟨v,hv⟩ := hp
  rw [show q = reflectPol _ (realForm p) from rfl,← hv,← real_eats,← pulls_label]; exact LinearMap.mem_range_self _ _

/-- Need the Ward sum at d, not larger. After feeding E p the Ward sum again
at d. Output commutator may still be in d+1, and one must *pay* for
`ghost` removal there. -/
theorem commute_ghost {L : Engine G 0} {T : Module.End ℂ (WickPol G)} (hd : 4≤d) (H : silence G d T)
    (ht : ∀ a b, T (polStress G a b)=0)
    (HL : ∀ (n : ℕ) (x : Points (n+1)), x∈conf _ → ∃ χ v, Table.Window x χ ∧ Motion (x:=x 0) v L χ)
    (p : WickPol G) (hp : p∈shellSector G d) (he : rewired L p∈shellSector G d) :
    rewired L (T p) - T (rewired L p) ∈ ghost G d := by
  intro n q x hq hx
  classical
  obtain ⟨χ,v,w,Hv⟩ := HL n x hx
  let B (p : WickPol G) := Fin.cons (α:=fun _ : Fin (n+1) => WickPol G) p q
  let f (i : Fin (n+1)) := update (B p) i (T (B p i))
  let R (i) := stressRead x v (f i)
  have hh : exportFlux (fun a y => ∑ i, R i a y) χ=0 := by
    rw [flux_invariant χ _ 0]
    · simp [exportFlux]
    intro a y hy
    have hu := Work.A01.window_separated hx w hy
    unfold R stressRead; rw [Finset.sum_comm];
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.smul_sum];
    suffices hr : (∑ i, bookend x y (f i) (polStress G a b))=0 by rw [hr, smul_zero]
    have hm (i : Fin (n+1)) : B p i ∈ shellSector G d := Fin.cases hp hq i
    have ha := H _ (Fin.cons (α:=fun _ => WickPol G) (polStress G a b) (B p)) (Points.cons y x)
      (fun i => Fin.cases (chain hd (stress_label G a b)) hm i) hu
    conv at ha => lhs; rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, ht] at ha
    rw [show moment G (Points.cons y x) (update (Fin.cons (α:=fun _ => WickPol G) (polStress G a b) (B p)) 0 0)=0 from
      MultilinearMap.map_coord_zero _ 0 (Function.update_self _ _ _),zero_add] at ha; refine Eq.trans ?_ ha
    apply Finset.sum_congr rfl; intro i _
    rw [book_eval,Fin.cons_succ]; congr 1
    exact Fin.cons_update ..
  rw [flux_series w.1 w.2.1] at hh
  · simp_rw [R,moment_force hx w Hv,Finset.sum_neg_distrib,neg_eq_zero] at hh
    rw [Fin.sum_univ_succ] at hh
    have ha := H (n+1) (B (rewired L p)) x (fun i => Fin.cases he hq i) hx
    rw [Fin.sum_univ_succ] at ha
    have hm (i : Fin n) : update (f i.succ) 0 (rewired L (f i.succ 0)) = update (B (rewired L p)) i.succ (T (B (rewired L p) i.succ)) := by
      ext1 b; unfold f B; simp only [Fin.cons_succ]; refine Fin.cases ?_ (fun j => ?_) b <;> simp
      · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero _)),Fin.cons_zero,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero _)),Fin.cons_zero]
      by_cases h : j=i <;> simp_all [Function.update]
    simp_rw [hm] at hh
    let F := ((moment G x).toLinearMap (B p) 0)
    have hg v : moment G x (B v) = F v := by unfold F; rw [MultilinearMap.toLinearMap_apply]; unfold B; rw [Fin.update_cons_zero]
    dsimp only [f,B] at hh ha
    simp only [Fin.cons_zero,Fin.update_cons_zero] at hh ha
    rw [show moment G x (Fin.cons (rewired L (T p)-T (rewired L p)) q)=_ from hg _, map_sub,sub_eq_zero,← hg,← hg];
    exact add_right_cancel (hh.trans ha.symm)
  intro i a y hy; exact tendsto_finsetSum _ fun b _ => petal_cost hx w a b _ Hv.symm hy
end YM.Maxwell.Free
