import YM.SharpGram.Lenses.Resolved
import YM.SharpGram.Measured

/-!
# Choose a diagonal not sacrificing k!

Nondecreasing horizon. All properties needed for the Weak Gram basis and
extra point estimates, kept in the same physical philosophy. Instead of one
fixed aperture scheme, make one simultaneous path for ALL finite demands
through the Coverage supplies. Special reflected point upgrade and related
local physical uses are below. Only conditional remaining need is sharp
change over true neighboring annuli; no assumption about reference norms is
made in this file. The universal subfilter remains unchanged from our choice
at all horizon stations.

Does not impose monotonicity on pricing radius, as choices may change width
through apertures and stages. Eventually comparable to `a k` with log
powers so fine for physical reading with charge. Point-comparison estimates
require continuity at ties and spatial derivatives, so an inexact tilt
argument alone won't do; arrive on arbitrary joint distributional tests after
using that tilt argument for access. Public estimate in Lenses.Sights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Lenses
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open PhysicalNext.RankCovariance Org Spec Next.UVStress Further.CorrectedLift MergeProof.East Weak
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
variable {u:Filter (ℕ×ℕ)}
local notation "S'"=> (Bel C.book)
local notation "P"=> C.path.levels.clock.hatBeta
local notation "σ"=> F.room.kernel.spin
local notation "θ"=> Maxwell.Free.spin_free C.labels
local notation "V"=> F.sector.derivatives

-- real correlation at exact length standard true filtration; consume after
-- adjustment. Reuse Spin.change, physical ALWAYS F.sector.*
abbrev price (d : ℕ) := 1+(d+1)+1
-- independent of aperture choice.
def margin (C : Family G) (d : ℕ) := (Weak.Portfolio.freely (C:=C) d).choose
def bonus (C : Family G) (d : ℕ) := Real.sqrt ((1+‖Portfolio.modelFull C d‖)/(margin C d / 2)) * 2
lemma bonused (C : Family G) (d : ℕ) : 0 ≤ bonus C d := mul_nonneg (Real.sqrt_nonneg _) zero_le_two

structure Costs (C : Family G) {S:Table C.book} (k d : ℕ) (u : Filter (ℕ×ℕ))
    (X:YM.Spin.change S d) : Prop where
  courtesy (x : S.Field d) : ∃ (y : C.label d) (q : ℕ×ℕ → C.label d), S.project d y=x ∧ Tendsto q u (𝓝 y) ∧
       ∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ C.path.levels.clock.hatBeta k^price d * C.S.a k ^ d * ‖X.symm x‖
  outlet (v : Filter (ℕ×ℕ)) [v.NeBot] (hc : v ≤ u) (q : ℕ×ℕ → C.label d)(x : C.label d)(z:ℝ) :
            (∀ᶠ i in v, quota C d k i.1 i.2 (q i) ≤ z) → Tendsto q v (𝓝 x) →
              ‖X.symm (S.project d x)‖ ≤ bonus C d / C.S.a k ^ d * z

structure Sleeve (U : ℕ) (B : Next.UVStress.Panel S) (h : ℝ) : Prop where
  ticket {n : ℕ} (hn : n ≤ U) (p : Caps n) (hp : ∀ i, p i ≤ U) (a : record C p) :
    ∀ t : Test n, tsupport t ⊆ Scaling.window (sizeHint U) _ → (∀ x, ‖t x‖ ≤ sizeHint U) →
      let v := hang p (depthWord p a)
      ‖t.applyTo (tested h B v - disc v)‖ ≤ costHint U

abbrev Canopy (S : Table C.book) := ∀ d : ℕ, YM.Spin.change S d
abbrev testLens (Y : Canopy (C:=C) S) : Panel S := fun d=>(Y d).toLinearMap
structure Ledger (u : Filter (ℕ×ℕ)) (k D : ℕ) (Q : Portfolio C F.room.cutoff D u)
    (Y : Canopy (C:=C) S) : Prop where
   -- include needed geometric prices at this k. No after-framing error can pay longer exponential
   -- product from moving query to fixed reference.
   switch : SubLimits C D (Q.atK k) Q.aperture u (Q.matrix k) (Q.field k)
   plume : Poised Q.p Q.labelsC F.room.cutoff Q.omega Q.j (trays D) Q.z (Q.atK k) (Q.matrix k)
   ge : Q.atK k ≤ k
   lower : C.S.a k ≤ Q.radius k
   shrink : Q.radius k ≤ costHint D
   bound : Q.radius k ≤ C.S.a k*(P k)^2
   -- note full rho geometry announcement depends on D; retain neighbor gap receipt.
   stretch : C.S.scale k ≤ C.S.scale (Q.atK k)+Real.log (P k)
   access (d : Fin (D+1)) : Costs C k d u (Y d)
   basis : Extra.WeakScaling.Graded V (Maxwell.Free.scheme C.labels) σ θ Y D
   leading : Sleeve D (testLens Y) (Q.radius k)

include F
variable [u.NeBot] (hf:u≤f.fuse) {D : ℕ} (Q : Portfolio C F.room.cutoff D u)
variable (S0 : OPE.Facilities C f S)
include Q hf S0
open Weak.Portfolio
set_option maxHeartbeats 700000 in
lemma ledges (hm : CanSmear Q) : ∃ Y : ℕ → Canopy S, ∀ᶠ k in atTop, Ledger F u k D Q (Y k) := by
   let hg:=S0.simpleGate
   obtain ⟨W,r,T₀,hr⟩:= S0.costlier
   let ht:= hr.toTableTickets
   obtain ⟨Y,H,He⟩:= Q.tune_grades F ht hf hg
   have hp (d:Fin (D+1)) : ∀ᶠ k in atTop, Costs C k d u (Y k d):=by
      let δ:= margin C d
      have he : 0<δ := (Weak.Portfolio.freely (C:=C) d).choose_spec.1
      let K:=δ/2+‖model C d‖
      have hx : 0 ≤ K := by unfold K; positivity
      filter_upwards [stayNear (Q.aligned F ht hf hg d (He d)) (half_pos he), Q.entry_cap_use F ht hf hg d K hx, Q.departUse F ht hf hg d (δ/2) (half_pos he)] with i hv hr hz
      exact ⟨hr (Y i d) (normBy hv),hz (Y i d) (absorb _ _ δ _ (Weak.Portfolio.freely (C:=C) d).choose_spec.2 (by simpa only [sub_half] using hv))⟩
   have hSize : 0 < sizeHint D := by unfold sizeHint; positivity
   have hr (n:Fin (D+1)) (t:Fin n → Fin (D+1)) (v:record C (fun i=>(t i).val)):=
     Q.progresses F hg ht hf hm Y He (t:=fun i=>(t i).val) ((Nat.le_of_lt_succ n.isLt).trans (Nat.le_add_right ..))
        (fun i=>Nat.le_of_lt_succ (t i).isLt) (depthWord _ v) |>.reads _ (window_closed (sizeHint D) n.val) (fun _ h=>spaced_conf (inv_pos.mpr hSize) h.1)
          (sizeHint D) hSize (costHint D) (cost_pos _)
   refine ⟨Y,?_⟩; filter_upwards [Q.onLevel,Q.length_power hg,H,eventually_all.mpr hp, (Q.detonates hg).eventually (ge_mem_nhds (cost_pos D)),eventually_all.mpr (fun i=>eventually_all.mpr (fun v=>eventually_all.mpr (hr i v)))]
      with k ⟨h1,h2,h3,h4⟩ hF hv ht hx hV
   refine ⟨h4,h3,h1,hF.1,hx,hF.2,h2,ht,hv,⟨fun {n} hn p hp a=> ?_⟩⟩
   let j : Fin (D+1) := ⟨n,Nat.lt_succ_of_le hn⟩
   exact hV j (fun i : Fin j=> (⟨p i, Nat.lt_succ_of_le (hp i)⟩:Fin (D+1))) a
omit S0 hf Q [u.NeBot]

structure Mantle (u : Filter (ℕ×ℕ)) where
  horizon : ℕ → ℕ
  grows : Tendsto horizon atTop atTop
  monotone_ : Monotone horizon
  lens : ℕ → Canopy S
  glassStation : ∀ k, Portfolio C F.room.cutoff (horizon k) u
  prices : ∀ᶠ k in atTop, Ledger F u k (horizon k) (glassStation k) (lens k)

omit F in
-- numerical exhaustion; doesn't shrink k, maintains monotonocity if desired
lemma advances (A : ℕ → ℕ → Prop) (h : ∀ d : ℕ, ∀ᶠ k in atTop,A d k) :
   ∃ B : ℕ → ℕ, Monotone B ∧ Tendsto B atTop atTop ∧ ∀ᶠ k in atTop,A (B k) k:=by
    choose M hM using (fun d=> eventually_atTop.mp (h d))
    let p : ℕ → Finset ℕ := fun k => (Finset.Iic k).filter (fun d=>M d ≤ k)
    let B k := (p k).sup id
    refine ⟨B,fun i j he=>Finset.sup_mono (fun v hv=> ?_),tendsto_atTop.mpr (fun d=>?_ ),?_⟩
    · obtain ⟨hx,hb⟩:=Finset.mem_filter.mp hv; exact Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hx).trans he),hb.trans he⟩
    · filter_upwards [eventually_ge_atTop (M d), eventually_ge_atTop d] with i hi he; exact Finset.le_sup (f:=id) (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr he, hi⟩)
    filter_upwards [eventually_ge_atTop (M 0)] with i hi
    have h0 : (p i).Nonempty:= ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (Nat.zero_le _),hi⟩⟩
    apply hM; apply (Finset.mem_filter.mp (show B i ∈ p i from ?_ )).2
    obtain ⟨v,hv,ht⟩:= Finset.exists_mem_eq_sup _ h0 id
    change B i= v at ht
    rw [ht]; exact hv

include S0
variable (v : Ultrafilter (ℕ×ℕ)) (hφ : (v:Filter _) ≤ f.fuse)
include hφ
theorem attains_mantle (hc : Dense.Coverage C F.room.cutoff) : Nonempty (Mantle F (v:Filter _)) := by
   choose Q0 hQ using fun d : ℕ=> smearsFromCoverage (D:=d) hc v hφ
   choose y hy using fun d=> ledges F hφ (Q0 d) S0 (hQ d) -- argument order
   obtain ⟨h,hh,hR,hT⟩:= advances _ hy
   exact ⟨⟨h,hR,hh,fun i=> y (h i) i,fun i=> Q0 (h i), hT⟩⟩
end YM.SharpGram.Lenses
