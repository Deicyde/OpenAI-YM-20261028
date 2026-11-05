import YM.MergeProof.East.Suds

/-!
# At weak-glass levels, inspect the actual full calibrated basis

Uses `lava_v`, as in `sight`; here apply to arbitrary `C.label`
instead of after `ladder`. Includes every off-shell input (which needn't be
in the image of ladder or detectable in the continuum; no asserting
positivity on those). Positivity will be used on the actual independent basis
AFTER projection and comparison. This lemma keeps the same price in estimates
of any of the mixed pairs thus produced. No mirror positivity at projection
ties is being read by it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage MergeProof MergeProof.East
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι]
  {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
open Analysis Next.UVStress Climb Ward

set_option quotPrecheck false
/-- Complete coefficient representation (unit normalization implicit in
`ladd`), not yet restricted to independent physical fields. Exact quota
read at k. -/
def microscope (C : Family G) (b : ℝ) (k : ℕ) (Y : ℕ → ℕ → TableL C D)
    (d : Fin (D+1)) (i : ℕ × ℕ) : Module.End ℂ (C.label d) :=
  ladd C (mag C.path.levels b k) k i.1 i.2 d (Y i.1 i.2 d)

variable (x : ι) {t : Fin (m+1) → Fin (D+1)}
  (v : (i : Fin (m+1)) → C.label (t i))
local notation "a!" => (P x).arc
local notation "a'" => C.S.a
local notation "ζ" => fun j => (mag A a! j)⁻¹
local notation "t0" => (fun i => (t i).val)
local notation "S1" => C.S
include H h hp hZ
-- Reading at ALL cutoff (eventually in N at fixed i, not just on the
-- given order). Then used on common fuse and its subfilters.
lemma inspect {T : Set (Points (m+1))} (hh:IsCompact T)(hz:T ⊆ conf _) (hn:2≤n) (he:m+1≤n) :
    ∃ κ:ℝ, ∀ᶠ k:ℕ in atTop, ∀ Y, Poised P B H O J n z k Y →
      ∀ i : Fin (m+1) → Cover, tag (ζ k) i ∈ T → tag (ζ k) i ∈ generic _ →
        ∀ᶠ N : ℕ in atTop, ∀ p : ℕ,
            ‖C.numeric N p (q_asked (C:=C) (d:=t0) (fun j => microscope C a! k Y (t j) (N,p) (v j)))
              (location C.S k N p ∘ i) - disc (jointX (d0:=t0) v) (tag (ζ k) i)‖ ≤ κ * Ship.budget A n k := by
    let O'(y) := Poly.price (fun _=>1) (Read.maxProfile C y (jointX (d0:=t0) v))
    have hT: ContinuousOn O' T:= by unfold O' Read.maxProfile Poly.price; exact continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((Read.profile_part_cont (S) (Maxwell.table_smooth C.labels) _ _).norm.mono hz)
    obtain ⟨c,hc⟩:=(hh.image_of_continuousOn hT).bddAbove
    obtain ⟨R,hR⟩:=(hh.image_of_continuousOn (show ContinuousOn (fun x=>(‖x‖:ℝ)) T from continuous_norm.continuousOn)).bddAbove
    let b:= (P x).arc; have hb:0<b:= by dsimp only [b]; linarith only [(P x).huge,Nat.cast_nonneg (α:=ℝ) D]
    refine ⟨c,?_⟩
    filter_upwards [lava_v P B H h hp O J z hZ v x (t:=t) hh hz hn he, open_read h hb R A (m+1)] with k he ha Y hY i hi hk
    let μ:= Next.Rank.Station.mag A b k; let y:= tag μ⁻¹ i
    have hA :Allowed A b k:=by obtain ⟨p,q,u,h⟩:= hY.supply x; unfold b; rw [← (P x).factor (C.path.levels.clock.J k)]; exact u.age.allot.permitted
    have hf:=ha hA i hk (hR (mem_image_of_mem _ hi)); change Fit A b k y at hf
    obtain ⟨h1,h2⟩:= authentic (V:=A) (b:=b) (k:=k) i
    filter_upwards [eventually_gt_atTop k,eventually_all.mpr (fun i => hf.stencils (F:=C) H (t i))] with N hj hx p
    let a : (q:Fin (m+1))→ C.label (t q) := fun i=> ladd C μ k N p _ (Y N p (t i)) (v i); let W := q_asked (C:=C) (d:=t0) a
    have he : ∀ s,s.val.Nonempty → (Ship.yard C b (show k ≤ N from hj.le) p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX (d0:=t0) v) W hf N p U).part s) ≤ Ship.budget (A) n k:=
      he Y hY N p hj y (h2.symm ▸ hi) hf
    have hr:∀ i,Interior _ (Read.probes C N p k (Next.Rank.Station.choose (A) b k y) W i):= fun i => (hx i).choose_spec p i (a i)
    have hu:= Read.full_cost H (Ship.fitting hf) (Ship.budget_pos (A) n k).le (Ship.yard C b (show k≤N from hj.le) p) hr he
    have hy : O' y ≤ c:= hc (mem_image_of_mem _ hi)
    change Next.Rank.Station.choose A b k y=i at h1; change Next.Rank.Station.tested A b k y=y at h2; rw [h1,h2] at hu
    exact le_trans hu (mul_le_mul_of_nonneg_right hy (Ship.budget_pos (A) n k).le)

variable {f : Extraction.Order} {Q : Table C.book} (U : Spec.Final C f Q)

include U
lemma actualRead {T : Set (Points (m+1))} (hh:IsCompact T)(hz:T ⊆ conf _) (hn:2≤n) (he:m+1≤n) :
    ∃ κ:ℝ, ∀ᶠ k:ℕ in atTop, ∀ Y, Poised P B H O J n z k Y →
      ∀ i : Fin (m+1) → Cover, tag (ζ k) i ∈ T → tag (ζ k) i ∈ generic _ →
        ∀ (q : Filter (ℕ×ℕ)) [q.NeBot], q ≤ f.fuse →
          ∀ w : (j : Fin (m+1)) → C.label (t j),
            (∀ j, Tendsto (fun l => microscope C a! k Y (t j) l (v j)) q (𝓝 (w j))) →
            ‖Q.classMoment Q t0 (tag (a' k) i) (fun j => Q.project (t j) (w j)) -
              disc (jointX (d0:=t0) v) (tag (ζ k) i)‖ ≤ κ * Ship.budget A n k := by
  obtain ⟨κ,hk⟩:= inspect P B H h hp O J z hZ x v hh hz hn he
  refine ⟨κ,?_⟩
  filter_upwards [hk] with k hk Y hY i hi hK u hu hQ w hT
  have hx: tag (C.S.a k) i ∈ generic _ := by
    have hy := scales_wild (gap_pos A a! k) _ hK
    rwa [show gap A a! k • _ = tag (C.S.a k) i from ?_] at hy
    ext j d; change (C.S.a k * mag A a! k)*(_ * _) = _*_; field_simp [(mag_pos ..).ne'] -- specify ζ
  rw [Q.class_agrees Q U.room.kernel.laws.toSymmetric (fun _ => le_rfl) t0 (generic_conf _ hx) w]
  let M (l:ℕ×ℕ) (j:Fin (m+1)) := microscope C a! k Y (t j) l (v j)
  have hM : Tendsto M u (𝓝 w) := tendsto_pi_nhds.mpr hT
  apply le_of_tendsto (((paid_point (t:=t0) M w hM hQ U.room.generic k i hx).sub_const _).norm)
  exact ((Push.RelayDifference.cutoff_grows f).mono_left hQ|>.eventually (hk Y hY i hi hK))|>.mono fun l h=> h l.2
end YM.SharpGram.Weak
