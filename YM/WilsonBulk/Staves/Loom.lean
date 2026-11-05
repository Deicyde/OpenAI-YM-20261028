import YM.WilsonBulk.Staves.Flags
import YM.Push.LOOP_COEFFICIENT.Color
import YM.Next.STATIONARY.Lift.Ward

/-!
# Constant color Ward and k-rank coherence. Keep complete all analytic powers
 without horizon dependency. On a finite stencil ledger generator reports all
 this covariance exactly. Tested through actual output front not orbit selection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Matrix LinearMap RG Precision Stationary Exterior Wilson Pert.Bulk Sheet Atelier
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {α β : Type} {p q σ : ℝ} {c d : Side} {u r n e : ℕ}

section orb
variable (k : G.El)
abbrev fret (v : α × Cloth G) : α × PotentialForm := (v.1,v.2.1)
abbrev selvedge (v : α × PotentialForm) (i : G.ColorIndex) : α × Cloth G:= (v.1,v.2,i)
-- finite homogeneous transform on `Book`
def rivet (c : Side) : Matrix (Pennant G c) (Pennant G c) ℝ:= Matrix.of fun i j=> if fret i=fret j then glass k i.2.2 j.2.2 else 0
def swatch (α : Type) : (α × PotentialForm) × G.ColorIndex ≃ α × Cloth G := Equiv.prodAssoc ..
lemma swatch_split [Fintype α] [AddCommMonoid β] (F : α × Cloth G→ β) : ∑ x,F x=∑ i:α×PotentialForm,∑ j:G.ColorIndex,F (selvedge i j):= by rw [← Equiv.sum_comp (swatch (G:=G) α) F,Fintype.sum_prod_type]; rfl
lemma riveted (x : Interface G c) (v : Site c × PotentialForm) (i : G.ColorIndex) : quill (rivet k c) x (selvedge v i)= G.adjoint k (traces G c 1 x v) i := by
  rw [quill,swatch_split]; change _= WithLp.ofLp (G.adjoint k (traces G c 1 x v)) i
  rw [matrices_real k]; simp [rivet,ite_mul,fret,selvedge,← Prod.ext_iff]; rfl
lemma rivet_signal (x : Interface G c) : signal G c (quill (rivet k c) x) = Lattice.gauge (Function.const _ k) (signal G c x) := by
  funext ⟨i,j⟩; apply G.mat_injective; simp only [Lattice.gauge,signal_at,G.mat_mul,G.mat_inv, Function.const_apply,G.mat_lieExp]; change _ = G.conjugate k (NormedSpace.exp (G.colorMat (traces G c 1 x (i,coord j)))); rw [← G.exp_conjugate,← G.mat_adjoint]
  congr 2; ext m; rw [traces_at]; exact riveted k ..
lemma Regime.glass_rank {I : Record (Pennant G c)} (hp : Document I) (h : Regime (volumeTape I)) : lecture (fun i j => rivet k c i j) I=I := by
  apply truthful (rivet k c) I hp;
  refine Eq.trans (h.dance.visitor (t:=fun _=>Function.const _ k) (Army.park _ _) rfl (v:=id) contDiffAt_id (quill_smooth _).contDiffAt rfl (quill_zero _) (Eventually.of_forall fun i=> rivet_signal k i)) ?_; rw [exposure_id, submit_id] -- name clash
-- complete color, then state charge

def ravel {G : Gauge} (k : G.El) {α : Type} (V : Page (α × Cloth G) n) (x : Legs (α×Cloth G) n) := ∑ i : Legs G.ColorIndex n,(∏ j:Fin n,glass k (i j) (x j).2.2)*V (fun j=>selvedge (fret (x j)) (i j))
def pile (α β : Type) (n : ℕ) : (Legs α n) × Legs β n ≃ Legs (α × β) n:= (Equiv.arrowProdEquivProdArrow ..).symm -- inspect
lemma loyal (P : Page (Pennant G c) n) (x : Legs (Pennant G c) n) :
    Sheet.travel (fun i j=> rivet k c i j) P x=ravel k P x := by
  let U : (Legs (Site c× PotentialForm) n)×Legs G.ColorIndex n ≃ Legs (Pennant G c) n := (pile ..).trans (Equiv.arrowCongr (Equiv.refl _) (swatch _))
  unfold Sheet.travel tele; rw [tsum_fintype,← Equiv.sum_comp U,Fintype.sum_prod_type,Finset.sum_eq_single (fret ∘ x)]
  · refine Finset.sum_congr rfl fun a _=>?_ ; unfold metal lot; congr 1; refine Finset.prod_congr rfl fun j _=> if_pos rfl
  · intro b _ hb; obtain ⟨i,hi⟩:= Function.ne_iff.mp hb; refine Finset.sum_eq_zero fun a _=>?_ ; unfold metal lot; rw [Finset.prod_eq_zero (Finset.mem_univ i) (show rivet _ _ _ _= _ from ?_),zero_mul]; exact if_neg hi
  simp
lemma Whisper.multirank {I : Library G} (h : Whisper I) (x : Legs (Mark G) n) (e : ℕ) : ravel k (I e n) x=I e n x := by
  cases n; simp [ravel,Unique.eq_default (α:=Legs (Mark G) 0)] -- syntax
  rename_i n; let D:=cascade (1:Side); let P:=(I e (n+1)); have hp:= (h.palm e (n+1)); have ht (x : Legs (Mark G) (n+1)) := Public.introduction P hp cascade_up x (Nat.succ_ne_zero _)|>(fun H:Tendsto (fun i=> coupon (D i) _ P (small (D i) _ ∘ x)) atTop (𝓝 (P x)) => H)
  refine tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum _ (fun i _=> (ht (fun j=>selvedge (fret (x j)) (i j))).const_mul (∏ j:Fin (n+1),glass k (i j) (x j).2.2))) (ht x) (Eventually.of_forall fun i=>?_)
  let T:= small (D i) (Cloth G); let L:= Sheet.issue (D i) I; change ravel k (L e (n+1)) (T ∘ x)= L e (n+1) (T ∘ x); rw [← loyal]; exact congr_fun (congr_fun (congr_fun ((h.guns _).glass_rank k (h.palm.at_issue _ h.style)) e) (n+1)) _
end orb
end YM.WilsonBulk.Parapet
