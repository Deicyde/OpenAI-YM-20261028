import YM.FullVolume.E6.Paid
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
variable (M:Bank)(I:Depot Q o x μ L C₀ K){χ:Chi}(Y:∀ n, Station M χ (I n) j)(h:Sweep K)
set_option quotPrecheck false
local notation "Hn"=> Bids M Q o χ j x K
include I Y h
lemma crew : ∃ v:ℕ→ℕ→ℝ,Sparse v∧∀ n i,Hn n (.inr (.inl i)) (v n i) :=by
    obtain ⟨v,hv,V⟩:= h.paidK; obtain ⟨b,hb,hr⟩:= boundCone M I Y; let B:= b*(1+((1:ℝ)+1))^j; have he: 1 ≤B:= one_le_mul_of_one_le_of_one_le hb (one_le_pow₀ (by norm_num)); refine ⟨_,hv.climb (zero_le_one.trans he), fun n i=>?_⟩
    constructor
    · intro F X hx heq hχ hM l z; let s:= X.liftA (K n|>.beta) z; let b:= X.enforce (2*o.a) s (X.plaza (Raw.forcedFoot S.ratio 0 X.B (K n).kin i)); change |(K n).k i (X.input s)*b| ≤ _; rw [abs_mul,abs_of_nonneg (show 0≤b from (X.conserve ..).1)]; exact (mul_le_of_le_one_right (abs_nonneg _) (X.conserve ..).2).trans ((V n i _).trans (le_mul_of_one_le_left (hv.value ..) he))
    intro F X hx hk hχ hM l z H E _ _ _ U s H' ht u; let b':=(K n).k i (X.input u); let L:= Brush.certified (k:=j) zero_le_one b' (x:=s)
    exact (((L.climb (show ‖b'‖ ≤ _ from V n i _) le_rfl).paints (hr n F X hx hk hχ hM z E U s H' ht (Raw.forcedFoot S.ratio 0 X.B (K n).kin i))).trim).climb (le_of_eq (by ring)) le_rfl
lemma whims : ∃ v:ℕ→ℕ→ℝ,Sparse v∧∀ n i,Hn n (.inr (.inr (.inl (.inl (.inl i))))) (v n i):=by
    obtain ⟨v,hv,V⟩:= h.paidE; obtain ⟨b,hb,hr⟩:= boundCone M I Y; let B:=b*(1+((1:ℝ)+1))^j; have hB: 1≤ B:= one_le_mul_of_one_le_of_one_le hb (one_le_pow₀ (by norm_num)); obtain ⟨D,hD⟩:= hv.bound; obtain ⟨C,hC,H⟩:= expandsP j (mul_nonneg (zero_le_one.trans hB) (budget_nonneg (hD 0)))
    let fa n i:= B*v n i; have hf n i:fa n i ≤ B*D:= mul_le_mul_of_nonneg_left (budget_single (hD n) i) (zero_le_one.trans hB)
    refine ⟨_,(hv.climb (zero_le_one.trans hB)).climb hC,fun n i=>?_⟩
    let R:=(K n).kin
    constructor
    · intro F X hx hk hχ hM l z; let s:= X.liftA R.beta z; let σ: LogIndex c f:= .inl (.inl i); let a:= X.farLog R o.a Q.table z σ
      have he: ‖a‖ ≤ fa n i:=by
          change |-R.activities.regularOccurrence R.p i (X.input s) * X.enforce _ s _|≤ _; rw [abs_mul,abs_of_nonneg (X.conserve ..).1, abs_neg]
          exact (mul_le_of_le_one_right (abs_nonneg _) (X.conserve ..).2).trans ((V n i _).trans (le_mul_of_one_le_left (hv.value ..) hB))
      exact (H ℝ (fun _=> a) _ 0 (hf n i) ((Brush.certified zero_le_one _).climb he le_rfl)).bound
    intro F X hx hk hχ hM l z hX E _ _ _ U p H' ht u; let s:= X.input u; let A:= -R.activities.regularOccurrence R.p i s; let L:= Brush.certified (k:=j) zero_le_one A (x:=p)
    have hz: ‖A‖ ≤ v n i:= by rw [Real.norm_eq_abs]; unfold A; rw [abs_neg]; exact V n i _
    exact H E _ _ _ (hf n i) (((((L.climb hz le_rfl).paints (hr n F X hx hk hχ hM z E U p H' ht (Raw.space (K n).tubes 0 X.B R (.inl i)))).trim)).climb (le_of_eq (by unfold B; ring)) le_rfl)
lemma stacked : ∃ v:ℕ→ LogIndex c f→ℝ,Sparse v ∧ ∀ n i,Hn n (.inr (.inr (.inl i))) (v n i):=by
    obtain ⟨u,hu,hU⟩:= gifts M I Y; obtain ⟨v,hv,h⟩:= whims M I Y h
    let w n (i:LogIndex c f):= Sum.elim (Sum.elim (v n) fun j=>u n (.inl (.inr j))) (fun j=>u n (.inr j)) i
    have he:Sparse w:= Sparse.either (Sparse.either hv (hu.pull (⟨_,Sum.inl_injective.comp Sum.inr_injective⟩ : _ ↪ _))) (hu.pull (⟨_,Sum.inr_injective⟩ : _ ↪ _))
    refine ⟨w,he,?_⟩; rintro n ((i|i)|i); exact h ..
    all_goals apply hU; simp [Loose]
lemma coined : ∃ v:ℕ→ Head S→ℝ, Coins M Q o χ j x K v:=by
    obtain ⟨u,hu,hS⟩:= merchant M I Y
    obtain ⟨v,hv,hL⟩:= dross M I Y
    obtain ⟨s,hs,hA⟩:= crew M I Y h
    obtain ⟨r,hr,hR⟩:= stacked M I Y h
    let w n : Head S→ℝ:= Sum.elim (u n) (Sum.elim (s n) (Sum.elim (r n) (v n)))
    have hz:Sparse w:= Sparse.either hu (Sparse.either hs (Sparse.either hr hv)); have he n (x:Head S):Hn n x (w n x):=by rcases x with i|i|i|i; exact hS ..; exact hA ..; exact hR ..; exact hL ..
    exact ⟨w,⟨hz,fun n F X hz hk hχ hM l z i=> (he n i).force F X hz hk hχ hM l z,fun n F X hz hk hχ hM l z i hv E _ _ _ V p H ht=> (he n i).regular F X hz hk hχ hM l z hv E V p H ht⟩⟩
end YM.ConnectedActivityE6.Lim
