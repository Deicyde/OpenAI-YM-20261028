import YM.RemainderComparison.Halo.Gala
import YM.RemainderComparison.Mosaic.Poems
import YM.RemainderComparison.Lyric.Finale

/-!
# At actual marker exposure with any real calibration nature
Baseline records with no extra calibration: take `s'=0`, e.g. and Z full. Others may be supplied at the same R census. Does not prove any physical need nor presentability of that input, producer RU. No assumption of affine estimate on those optional inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Muse
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic
variable (N:Captain H j q d v u A b r B e n χ)
local notation "B₀" => tile M H χ
local notation "E₀" => etude M H χ
local notation "A₀" => panel M H χ
local notation "L₀" => jewel M H χ
local notation "P₀" => parade M H χ

local notation "sx"=> radiusB x
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Mixed

-- Nature aperture at small calibration δ; marks potentially large.

def sits : ι→ℝ:= Verse.marked Zᶜ δ*l
def desk (t:ℝ) : ι→ℝ:= Verse.marked Z t⁻¹ * sits Z l δ
lemma trued (t:ℝ)(ht:0<t): Verse.marked Z t* desk Z l δ t=sits Z l δ:=by
   funext i; unfold Verse.marked desk; by_cases h:i∈Z <;> simp [*,Verse.marked,ht.ne']

lemma draped {Y:ℝ}(ht:0<Y) : sits Z l δ = Verse.marked Zᶜ (Y*δ) * (Verse.marked Z Y * Lyric.mulScale Y⁻¹ l):=by
   funext i; unfold Verse.marked Lyric.mulScale sits Verse.marked; by_cases h:i∈Z <;> simp [*,ht.ne']; field_simp
lemma descans {Y:ℝ}(hδ:0≤δ)(hτ:Y*δ≤1)(hY:0<Y)(hp:∀ i,0≤l i) : (∀ i,0≤desk Z l δ Y i)∧ desk Z l δ Y ≤ Lyric.mulScale Y⁻¹ l:=by
   constructor
   · intro i; unfold desk sits Verse.marked; specialize hp i; by_cases h:i∈Z <;> simp [*, mul_nonneg]
   intro i; unfold desk sits Verse.marked Lyric.mulScale; by_cases he:i∈ Z <;> simp [*]; apply mul_le_mul_of_nonneg_right _ (hp i); rw [← one_div]; exact (le_div_iff₀ hY).2 (by rw [mul_comm]; exact hτ)

lemma scores (p:H.fragrances)(i:Syllable M H p): (E₀ p i).letters.card=Lyric.notes M H p i:=by
   have e (f:Option (Fin p.fst)→Multiset ι)(s:Finset (Option (Fin p.fst))): (∑ j∈s,f j).card=∑ j∈s,(f j).card:=by
     induction s using Finset.induction_on with
     | empty=> simp
     | @insert j s hj ih=> simp [hj,ih]
   unfold Lyric.notes; exact e (fun j=> (tile M H χ (p.2 j).val (i j)).letters) univ
def clinic (p:H.fragrances)(w:Syllable M H p):= (E₀ p w).letters
local notation "G'"=> clinic M H χ
open Verse
lemma load_sum (p : Multiset ι): load Z p+load Zᶜ p=p.card:=by induction p using Multiset.induction_on with
   | empty=>simp [load]
   | cons i s he=>
      simp only [Verse.load,Set.mem_compl_iff] at he ⊢
      by_cases h:i∈Z <;> simp [*] <;> omega

abbrev virgin (p:H.fragrances) (w:Syllable M H p):= Verse.load Zᶜ (clinic M H χ p w)=0
abbrev arity (p:H.fragrances)(w:Syllable M H p):=Verse.load Z (clinic M H χ p w)
lemma harmonic (p:H.fragrances)(w:Syllable M H p): arity M H χ Z p w + Verse.load Zᶜ (G' p w)=Lyric.notes M H p w:=(load_sum Z _).trans (scores M H χ p w)
variable [Fintype ι]
open Next.Foundations
local notation "Lt"=> sits Z l δ
lemma orders (u:H.ThinP→Drums M S→ℝ) (hl:Lyric.Paid M H χ N u) (h:∀ i,0 ≤ l i) (hs :0≤δ)(Y:ℝ)(hY: 1≤ Y)(hd : Y*δ ≤1) {b:ℝ}
    (hV: Ac.Hit (Captain.reachability (H:=H)) sx (fun z=>∑ w:Syllable M H z,Lyric.Bill M H u z (Lyric.mulScale Y⁻¹ l) j w J) a b) :
    Ac.Hit (Captain.reachability (H:=H)) sx (fun z=>∑ w:Syllable M H z, if ¬ virgin M H χ Z z w ∧ arity M H χ Z z w≤I then Lyric.Bill M H u z (Lt) j w J else 0) a (Y^I * Y * b * δ):=by
   let l':=Lyric.mulScale Y⁻¹ l; let Y':=Y*δ; have hy:0<Y:=zero_lt_one.trans_le hY
   have he:0≤Y':= mul_nonneg hy.le hs
   have hx z (w:Syllable M H z) : Lyric.Bill M H u z (Lt) j w J = (Y'^load Zᶜ (G' z w)*Y^arity M H χ Z z w)*Lyric.Bill M H u z l' j w J:=by
      unfold Lyric.Bill; simp_rw [← Mosaic.pieces M H χ, draped Z l δ hy,Verse.extension]; unfold Y' arity clinic l'; ring -- ambiguity
   have hk z (w:Syllable M H z):0 ≤ Lyric.Bill M H u z l' j w J:=mul_nonneg (prod_nonneg fun i _=>prod_nonneg fun i _=>mul_nonneg (inv_nonneg.mpr hy.le) (h _)) (Lyric.dividend_nonneg M H χ hl z w)
   intro i; refine budget_loosen (budget_mono (budget_scale (show 0 ≤ Y'*Y^I from by positivity) (hV i)) ?_ ?_) (show _ ≤ _ from (by unfold Y'; apply le_of_eq; ring))
   · intro z; split; next h=>exact mul_nonneg (sum_nonneg (fun i _=> by split; rw [hx]; exact mul_nonneg (by positivity) (hk _ _); exact le_rfl)) (Real.exp_pos _).le
     next=>exact le_rfl
   intro z; dsimp only; split; next h=>
     rw [← mul_assoc, Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; refine sum_le_sum ?_; intro w _; split; next h=>
        rw [hx]; apply mul_le_mul_of_nonneg_right _ (hk _ _); have hp : 1 ≤ Verse.load Zᶜ (G' z w) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h.1)
        have hh : Y'^Verse.load Zᶜ (G' z w) ≤ Y':= by nth_rw 2 [←pow_one Y']; exact pow_le_pow_of_le_one he hd hp
        exact mul_le_mul hh (pow_le_pow_right₀ hY h.2) (by positivity) he
     next=> exact mul_nonneg (by positivity) (hk _ _)
   next=>rw [mul_zero]
end YM.RemainderComparison.Muse
