import YM.Pert.Parity.Branch
import YM.Pert.Rigid.Camera
/-!
Through five first order (and each odd order) is already zero exactly before large volume, since only even-slot labels occur in those horizons. With a fair position solve this persists for the centered output series (not asserting all its other orders admit a regulator limit).
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Pert.Parity
open Labels Position RawLabels Lattice Full Rigid UVNext.FreeStress Maxwell Filter Topology
open scoped Topology Classical
variable {G : Gauge} {d j l : ℕ} (F : Frames G)
lemma bond_even (p : Place j) (q : Place l) (h : j+l+4 ≤ d) : wash G d (bond p q h) = bond p q h := by
  refine Subtype.ext (eval_ext _ _ ?_); intro A
  change Labels.read A (shadow G (UVNext.FreeStress.tape p q))=Labels.read A (UVNext.FreeStress.tape p q)
  rw [shadow_read, UVNext.FreeStress.eval_tape, UVNext.FreeStress.eval_tape]; simp
lemma wash_four (hG : G.Simple) : wash G 4 = LinearMap.id := by
  apply LinearMap.ext_on (UVNext.FreeStress.spanFour hG)
  intro x hx
  rcases hx with hx|⟨u,v,hx⟩
  · rw [hx,wash_unit];rfl
  · rw [hx]; exact bond_even _ _ (by decide)
lemma wash_five (hG : G.Simple) : wash G 5 = LinearMap.id := by
  apply LinearMap.ext_on (UVNext.FreeStress.spanFive hG)
  intro x hx
  rcases hx with hx|⟨u,v,hx⟩|⟨u,v,w,hx⟩
  · rw [hx,wash_unit];rfl
  · rw [hx]; exact bond_even _ _ (by decide)
  rw [hx]; exact bond_even _ _ (by decide)
lemma Coat_even (hG : G.Simple) (w : d≤5) (v : E F d) : Coat F d v=v := by
  by_cases h : d<4
  · obtain ⟨t,rfl⟩ := below F hG h v; rw [map_smul,Coat_unit]
  have : wash G d = LinearMap.id := by interval_cases d;exact wash_four hG; exact wash_five hG
  rw [Coat_def,this,LinearMap.id_apply,physical_round]
variable {F} {k : ℕ} (Q : Conditions F d k)
lemma low_rows_fixed (hg : G.Simple) (hd : d≤5) : reverseRows Q = Q := by
  unfold reverseRows
  rw [show (fun i j=> Coat F d (Q.columns i j)) = Q.columns from funext fun i=>funext fun j=>Coat_even F hg hd _]
theorem minus_id_forces {V : Type*} [AddCommGroup V] [Module ℝ V] {v : V} (h : (-1:ℝ) • v = v) : v=0 := by
  have he : (2:ℝ) • v=0 := by rw [two_smul]; nth_rw 1 [← h]; simp [neg_one_smul]
  calc v = (2:ℝ)⁻¹ • ((2:ℝ) • v) := by rw [smul_smul]; norm_num
       _ = 0 := by rw [he,smul_zero]
/-- Here also without determinant or clean profile hypotheses. -/
theorem low_read (hg : G.Simple) (hd : d≤5) {σ} (X : Conditions F d σ) (L : Side) (m j) (h : Odd j) : finite X L m j = (0 : Ledger X) := by
  suffices hi : pull X (finite X L m j) = finite X L m j by rw [pull_finite,Odd.neg_one_pow h] at hi;exact minus_id_forces hi
  funext i z
  let w := (fun j=> baring F d (z j))
  have e := decode_map X i ((PowerSeries.coeff j).compMultilinearMap (Full.profile d (X.arity i) F L m (X.profiles i))) (finite X L m j) (fun _=>rfl) w
  exact (by change decode X (finite X L m j) (fun j=> Coat F d (w j))= _; simp only [Coat_even F hg hd];exact e)

theorem low_response (hg : G.Simple) (hd : d≤5) {σ} (X : Conditions F d σ) {φ : Ledger Q→Buffer F d} {J} (h : Fair Q J) (H : Reports (chart Q) (white Q) 0 φ) (L : Side) (p j) (hQ : CleanProfiles Q) (hL : 1 < L.val) (h0 : Odd j) :
    ∀ᶠ i in atTop, readJet φ p j (chart X) (finite Q L i) (finite X L i)=0 := by
  filter_upwards [position_sign h H L hQ hL X p j] with i hi
  rw [low_rows_fixed X hg hd,Odd.neg_one_pow h0] at hi; exact minus_id_forces hi.symm
end YM.Pert.Parity
