import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Flux
import YM.AnalyticBridge.RESET_INCOME_PORT.Fiber
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Recenter
import YM.Further.CURVED_GAUSSIAN_JETS.Awards
import YM.Further.CURVED_GAUSSIAN_JETS.Bands
import YM.Further.CURVED_GAUSSIAN_JETS.Branch
import YM.PhysicalNext.ORDERED_AFFINE_2B.Match
import YM.PhysicalNext.ORDERED_AFFINE_2B.Receipts
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Grant
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Reset

/-!
# Obtain the books/port on the given Teller/Plate history

N is paid at the ACTUAL endpoint-window scale (inner in native f,
outer in coarse c), not at some sufficiently large number after V. This
file buys the spectral and kernel portion on every usable family at this
post-L delay. Supports tax also bought for further use. To attach these
to the physical scalar still need the same-purchase agreements and flag,
ratio/door etc. hypotheses later. Not paying for whole Steps/schedule. No
hypothesis of a supplied common issue satisfying independent witnesses
after the V query. The underlying proofs quantify uniformly in ALL periods
with room before encountering them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree AnalyticBridge AnalyticBridge.Covariance Terrain
open AnalyticBridge.ResetIncome SectorTools.ActualScalar
open Next Next.Fluctuations Next.SectorChange
open Further Further.CurvedGaussianJets Jets ChangeV Tracks
open Push.SectorMeasure Matrix Receipts Progress.StationaryScenes
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

-- script lengths in TWO systems. watch fixed even under rerating.
def rail (x : ℝ) := radiusB x/100
abbrev watch : ℕ := 3004

lemma spent (S : StepData c f) (G : Gauge) (x : ℝ) (hb : 120 ≤ radiusB x) :
    (windows S G x hb).Includes (initial G f) (rail x) ∧ Nearby (windows S G x hb) (home S) (3000*rail x) := by
  refine ⟨fun i j hij=>?_,fun i j hij=>?_⟩
  · rw [wind]; intro p hp q hq
    apply (separation_triangle p (home S i) q).trans
    have he := Work.E04.parent_separation S.ratio (initial G f j) (initial G f i)
    rw [separation_comm (initial G f j)] at he; change separation (home S j) (home S i)≤ _ at he
    have hh : separation p (home S j)≤1 := (separation_comm ..).trans_le (meetings j.1 hp)
    have hx : separation (home S i) q≤1 := meetings i.1 hq
    have hh' := separation_triangle p (home S j) (home S i); unfold rail at *; omega
  have hh : j ∈ unitWin S x i := (wind ..).1 hij
  apply (aboutWin hh).trans; unfold windowR rail; omega

structure Tab where
  v : CurvedGaussianJets.Prices
  δ : ℝ
  work : ℝ
  K : ℝ
  expo : 0 < δ
  budget : 1 ≤ K

namespace Tab
abbrev fee (J : Tab) (G : Gauge) (f : Side) (q : ℕ) (o : Site f) {z : ℝ} (hz : 0 ≤ z) : Jets.Weights (initial G f) :=
  rule (initial G f) o q hz J.expo
abbrev carries (J : Tab) (q n : ℕ) (o : Site f) {z : ℝ} (hz : 0 ≤ z) (S : StepData c f) (U : Config G c)
    (X : Jets.Field G c (Thing G f)) := Street J.v (J.fee G f q o hz) n (Due S.ratio.embed o q z) X U J.work

structure Ships (J : Tab) (q n : ℕ) (σ : ℝ) (T : Tube G S) (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (x : ℝ) (V : Config G c) : Prop where
  near (o : Site f) {z : ℝ} (hz : 0 ≤ z) : ∀ᶠ U in 𝓝 V,
    J.carries q n o hz S U (charter T x A F k) ∧ J.carries q n o hz S U (fun _=> flat T x F k)
  yard : lengthA S.patch x ≤ 4*rail x
  branch : S.patch.Branches S.kernel G
  tall : 120 ≤ radiusB x
  port (o : Site f) {z : ℝ} (hz : 0 ≤ z) : Port J.v (J.fee G f q o hz) n J.work J.K (rail x)
  riders : Hits (initial G f) S.ratio J.v σ J.K watch (rail x)
end Tab

lemma ready_at (e : Plate G S) (ht' : 100*(1+radiusB e.x) ≤ c.val) (ht : S.patch.Branches S.kernel G) (hx : macroR S.patch + Pockets.extent S.patch+predReach S.patch ≤ radiusB e.x) (A : Stores S) (V : Config G c) (hv : e.matched A V) :
    Pockets.Paid S G ∧ Shape.Covered (held e A) (temp e.x) V := by
  constructor
  · have hc : c.val ≤ f.val := S.sizes ▸ le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
    exact ⟨⟨ht,by omega,by omega⟩,by omega⟩
  intro i p hp
  have hi := i.property
  rw [←show A.flags=RG.flags (temp e.x) V from hv] at hp
  rw [held_iff] at hi
  by_contra! hg; apply hi
  left; apply halo_spec.mpr
  exact ⟨p, Finset.mem_union_right _ hp, (separation_comm ..).trans_le (by omega)⟩

lemma one_matches (e : Plate G S) : e.matched noHole 1 := by
  ext p; simp only [noHole,RG.flags_spec]; constructor
  · simp
  rintro ⟨b,h,hb⟩; simp [faceValue,square,travel] at hb
  exact False.elim ((not_lt_of_ge (temp_nonneg _)) hb)

lemma remembered (e : Plate G S) (he : Doors e) (k : S.Choices) {Pt : Teller G} (hT : Pt.Funds S e.tube) (hV : Mapper.Checks e.x k noHole e.forest (1:Config G c)) :
    (page e he noHole k 1).sigma 1 = Actual.initial e.tube.up e.tube.high (Stores.till e.x) e.forest := by
  rw [Mapper.full_exact _ _ _ _ _ _ hT hV,show held e noHole=∅ from Finset.eq_empty_of_forall_notMem (clear _)]
  exact Mapping.initial_mount _ _ _ _ _ (funds_branch hT) k

-- exposes both paper equality to the flat benchmark and eligibility of
-- the full family. Use that exact paper, don't compare different Q reads.
structure Delivery (J : Tab) (q n : ℕ) (σ : ℝ) (e : Plate G S) : Prop where
  flat (he : Doors e) (k : S.Choices) : (page e he noHole k 1).sigma 1 = e.Flat
  issue (he : Doors e) (A : Stores S) (V : Config G c) (k : S.Choices) : e.matched A V →
    (∀ᶠ U in 𝓝 V, Mapper.Checks e.x k A e.forest U) ∧ J.Ships q n σ e.tube e.forest A k e.x V

/-- Order, growth and support-rate requirements stipulated for this
actual Teller before entering a period. Can buy arbitrarily large fixed
orders, then wait. Use at e with actual positive Doors, shared flag table
and e.tube from THIS call. Not issuing the paths/choices from unattained
pre-L conditions or doing any hard-extension analysis here.
-/
theorem issuance (G : Gauge) (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) (q n : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ J : Tab, ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (e : Plate G S), e.x=x → S.patch=P →
      100*(1+radiusB x)≤c.val → Pt.Funds S e.tube → Delivery J q n σ e := by
  obtain ⟨v,M,ε,δ,hδ,hM,hε,h⟩ := ChangeV.route G P Pt.bind Pt.top.clip q n Pt.top.paths Pt.top.width_pos
  let v' := revised v (things G); let m := max 1 (max v.mass M)
  let d := smaller v (things G) n; have hd : 0<d := small_pos ..; have hm : 0 ≤ m := zero_le_one.trans (le_max_left ..)
  obtain ⟨K,hK,hE⟩ := enroll v' n (rule (fun _ : Unit=> (0:Site 1)) 0 q zero_le_one hd) hm
  let J : Tab := ⟨v',d,m,K,hd,hK⟩
  have ht : Tendsto rail atTop atTop := tendsto_atTop.mpr fun p=> (Work.E01.radiusB_tendsto.eventually_ge_atTop (100*p)).mono fun x hx=>by unfold rail; omega
  have hu : Tendsto temp atTop (𝓝 0) := by simpa using! Work.E09.radiusB_temp 0
  refine ⟨J,?_⟩
  filter_upwards [ht.eventually hE, ht.eventually (hit_time watch v' hK hσ), Mapper.check_zone G P Pt.bind hP,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (120+macroR P+Pockets.extent P+predReach P), Terrain.reasonably P,
    hu.eventually_le_const hε] with x hN hQ hh hy hz hε'
  intro c f S e hp hS hR hT; subst x
  obtain ⟨a,b,hW,_⟩ := hT.feeds
  have hG := hh S hS hT.knobs hR
  have hx := funds_branch hT
  have hb (l : S.Choices) := (hG l noHole e.forest 1 (one_matches e)).self_of_nhds
  constructor
  · intro he k; rw [← flat_price_eq e he hx,benchmark,remembered e he k hT (hb k),remembered e he e.tag hT (hb _)]
  intro he A V k hV
  have hs := hG k A e.forest V hV
  let E := allThings e.forest G; let H := held e A
  let R := Stores.till e.x
  obtain ⟨ha,hA⟩ := ready_at e hR hx (by rw [hS]; omega) A V hV
  have hX : (fun U => Joint.place E (Joint.join (precise H k e.tube.up Pt.top.clip R U) 1)) =ᶠ[𝓝 V] charter e.tube e.x A e.forest k := hs.mono fun U hu=> by
    unfold charter; rw [across e he A k U (Y:=1),Mapper.full_exact _ _ _ _ _ _ hT hu,hT.high]
  have hB : (fun _ : Config G c=> Joint.place E (Joint.join (Actual.initial e.tube.up Pt.top.clip R e.forest) 1)) = fun _ => Whole.flat e.tube e.x e.forest k := funext fun U=>by
    unfold Whole.flat; rw [across e he noHole k 1 (Y:=1),remembered e he k hT (hb _), hT.high]
  let p := initial G f
  have hg : Push.Uniform.Multiplicity p (things G) := numerous G f
  refine ⟨hs,⟨?_,by rw [hS]; unfold rail; have := hz.1; omega,hx,by omega,fun o z h => hN.use rfl,hQ S.ratio (Thing G f) p hg⟩⟩
  intro o z ht'
  have hu := h S hS hT.knobs ha e.forest H V (temp_nonneg _) hε' hA ht' o k e.tube.up hW R
  filter_upwards [hu.2,hX.eventually_nhds] with U hU ht
  obtain ⟨h₁,h₂⟩ := flat_streets hU hu.1
  have hloc : Green.address (G:=G) e.forest = p ∘ E ∘ Sum.inl := rfl
  rw [hloc] at h₁ h₂
  exact ⟨consume (Receipts.budget E h₂ hg) ht,hB ▸ Receipts.budget E h₁ hg⟩
end YM.PhysicalNext.OrderedAffine2B.Whole
