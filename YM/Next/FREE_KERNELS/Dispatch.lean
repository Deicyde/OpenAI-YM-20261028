import YM.Next.FREE_KERNELS.PatchMean
import YM.Next.FREE_KERNELS.Sprout

/-!
# Transferring from all cubic fibers

A `Corresponds` package only used for before-L analytic row producers.
These bridge lemmas do not assume corpses of identities on small-period
tori extend to symbols. Includes cross-row conventions for L-normalized
columns *returning to* counting measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG
open scoped Topology BigOperators ComplexConjugate

variable {c f : Side} {α β γ : Type*}

/-- Cochain kernel identification receipt, on real fundamental cube.
This suffices for running the finite matrices. -/
structure Corresponds (R : Row α β) (f : Momentum → Matrix α β ℂ) : Prop where
  safe : R.safe
  echo p : p ∈ baseCube → R.read p=f p

def solo (c : Side) (f : Momentum → Matrix α β ℂ) := fiber (fun p : Site c => f (mon p))
def braceAll (r : Ratio c f) (f : Momentum → Matrix α β ℂ) :=
    fiber fun p : Site c => fiber fun l : Site r.count => f (aliasAt (mon p) l)

variable [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace Corresponds
variable {R : Row α β} {F : Momentum → Matrix α β ℂ}
lemma coarse (h : Corresponds R F) (c : Side) : Runs (rotations c α) (rotations c β) (R.acts c) (solo c F) := by
  unfold Runs; rw [circulant c R h.safe]; unfold solo; simp_rw [h.echo (mon _) (mon_mem c _)]
lemma fine (h : Corresponds R F) (r : Ratio c f) (hr : Odd r.count.val) : Runs (readings r α) (readings r β) (R.acts f) (braceAll r F) := by
  unfold Runs; rw [aligns r R h.safe]; unfold braceAll direct; simp_rw [h.echo (aliasAt _ _) (alias_base (mon_mem c _) _ hr)]
end Corresponds

variable {j t : ℕ}
lemma heart_banked {ι : Type*} (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (v : ι → Train j) :
    ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ i, (record (pulse k (v i))).strip σ C ∧ (record (vault k (v i))).strip σ C := by
  obtain ⟨ha,hb⟩ := heart_budget k hk hj v
  obtain ⟨σ,C,hp,hc,h⟩ := matrix_cover ha zone_pos (fun _ _ h x hh => (overlap_heart _ hk _ h x hh).1)
  obtain ⟨θ,D,ht,hd,g⟩ := matrix_cover hb zone_pos (fun _ _ h x hh => (overlap_heart _ hk _ h x hh).2)
  refine ⟨min σ θ,max C D,lt_min hp ht,lt_max_of_lt_left hc,fun i => ⟨fun x y => ?_,fun x y => ?_⟩⟩
  · exact (h i x y).mono (min_le_left ..) ((mul_one _).trans_le (le_max_left ..))
  exact (g i x y).mono (min_le_right ..) ((mul_one _).trans_le (le_max_right ..))

lemma heart_true (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (v : Train j) :
    Corresponds (record (pulse k v)) (pulse k v) ∧ Corresponds (record (vault k v)) (vault k v) := by
  obtain ⟨η,C,hη,hC,H⟩ := heart_banked k hk hj (id : Train j → _)
  obtain ⟨ha,hb⟩ := heart_budget k hk hj (id : Train j → _)
  exact ⟨⟨Row.rights _ _ (H v).1 hη.le,fun p hp => record_eq ha zone_pos v
    (fun i p h x hh => (overlap_heart k hk _ h x hh).1) (fun i p h => (heart_real k hk _ h).1) hp⟩,
    ⟨Row.rights _ _ (H v).2 hη.le,fun p hp => record_eq hb zone_pos v
    (fun i p h x hh => (overlap_heart k hk _ h x hh).2) (fun i p h => (heart_real k hk _ h).2) hp⟩⟩

namespace Flight
variable (P : Flight j t) (K : KernelChoices) {c f : Side} (hc : f.val=c.val*P.L.val)

def visit : StepData c f := ⟨P.patch,K,hc⟩
abbrev visitRatio : Ratio c f := ⟨P.L,hc⟩

def fromBank (w : Thread j t α β) (e : ℕ) (p : Momentum) := downAlias fun l : Site P.L => toll P.L e • w P p l

def going (p : Momentum) := upAlias fun l : Site P.L => (P.L.val:ℂ) • hinges P 1 (aliasAt p l)
lemma phi_run : Runs (rotations c (TypeFace 1)) (readings (P.visitRatio hc) (TypeFace 1))
    (mean (visit P K hc)) (solo c (going P)) := by
  have hm p : mask 1 (fun i => pullLine P.patch i p)=hinges P 1 p := by
    unfold pullLine hinges; rw [mask1_scale]; rfl
  have he := patch_service (visit P K hc)
  change Runs (rotations c _) (readings (P.visitRatio hc) _) _ (fiber fun p : Site c => upAlias fun l : Site P.L =>
      (P.L.val:ℂ) • mask 1 (fun i => pullLine P.patch i (aliasAt (mon p) l))) at he
  simp_rw [hm] at he; exact he

lemma sail_run {w : Thread j t α β} (h : Secured w) (hj : 4≤j) (e : ℕ) :
    Runs (readings (P.visitRatio hc) α) (rotations c β) (installed (P.visitRatio hc) (meshBook w e [] P))
      (solo c (P.fromBank w e)) := by
  let r := P.visitRatio hc
  let M := meshBook w e [] P
  have he (p : Site c) : M.read (mon p)=aliasBlock P.L α (mon p)* P.fromBank w e (mon p) := by
    ext ⟨a,i⟩ b
    rw [show M.read _ (a,i) b=_ from h.bankRead hj e (show [].length≤j-2 from Nat.zero_le _) P a (mon_mem c p) i b, mul_apply,Fintype.sum_prod_type]
    unfold spread aliasBlock fromBank downAlias listChip; simp [Matrix.sum_apply,ite_mul]
  have hx : parsed r α*solo c (P.fromBank w e)=solo c M.read := by
    unfold parsed solo; rw [fiber_mult];
    congr! 2 with p; exact he p |>.symm
  unfold Runs; rw [assembled r M (h.bankSafe hj e (show [].length≤j-2 from Nat.zero_le _) _),readings,Matrix.mul_assoc,hx]; rfl
end Flight

lemma cobound_true (r : ℕ) : Corresponds (cobound r) (signal 1 r) := by
  refine ⟨cobound_safe r,fun p _ => ?_⟩; rw [signal_unit,Exterior.reading]
lemma runs_rotor (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (v : Train j) (n : Side) :
    Runs (rotations n (TypeFace 1)) (rotations n (TypeFace 1)) (Precision.K ((record (pulse k v)).acts n)) (solo n (rotor 1 k v)) := by
  let D := (cobound 1).acts n
  have hh := (cobound_true 1).coarse n
  have hx := hh.back (rotations_crew n _) (rotations_crew n _)
  have ht := (hx.product ((heart_true k hk hj v).1.coarse n)).product hh
  rw [div_self (stage_ne n),one_smul] at ht
  unfold solo at ht; simp only [fiber_H,fiber_mult] at ht
  unfold rotor; have hm (p : Site n) := mirage_herm 1 (mon p) (real_frequency p) 1
  unfold solo; simp_rw [hm]; exact ht
lemma runs_rotor_fine (k : ℝ) (hk : 0<k) (hj : 4≤j) (v : Train j) (s : Ratio c f) (hs : Odd s.count.val) :
    Runs (readings s (TypeFace 1)) (readings s (TypeFace 1)) (Precision.K ((record (pulse k v)).acts f)) (braceAll s (rotor 1 k v)) := by
  have hh := (cobound_true 1).fine s hs
  have hx := hh.back (readings_crew s _) (readings_crew s _)
  have ht := (hx.product ((heart_true k hk hj v).1.fine s hs)).product hh
  rw [div_self (stage_ne f),one_smul] at ht; unfold braceAll at *
  simp only [fiber_H, fiber_mult] at ht
  have hm (p : Site c) (l : Site s.count) : (signal 1 1 (aliasAt (mon p) l))ᴴ=mirage 1 1 (aliasAt (mon p) l) := (mirage_herm _ _ (alias_real (real_frequency p) l) _).symm
  simp_rw [hm] at ht; exact ht
end YM.Next.Free
