import YM.RemainderComparison.Mosaic.Dollars

/-!
# Exact same density law all V

Switch interpolation at each p pays genuine Price. Substituting Marker.Poly
retains singleton and finite source multiplicity on each utterance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Mosaic
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves Merge Palette Next.Scheduling
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Lyric
variable (N:Captain H j q d v u A b r B e n χ)
open Verse
local notation "B₀" => tile M H χ
local notation "E₀" => etude M H χ
local notation "A₀" => panel M H χ
local notation "L₀" => jewel M H χ
local notation "P₀" => parade M H χ

local notation "sx"=> radiusB x
variable (Z:Set ι)(l:ι→ℝ)
open Mixed
local notation "l'"=> Verse.wave Z l
open Marker Switch
variable {τ:Type} [DecidableEq τ] {Jm:Census τ} (z:ι→Poly Jm) (hZ:∀ i,z i*z i=0)

-- Input pointwise integrity uses Budget β. Prove for all sell.L
include H hZ
set_option quotPrecheck false
local notation "f'" => fun V:Config G f=>∑ p:Drums M S,(raw M p).paint Z l z V
lemma band (U:Config G c): S.push R.beta (f') U=sound z (fun t v=>S.push R.beta (buy M (l' t v) S) U):=by
   let X:= S.push (G:=G) (X:=ℝ) R.beta -- check parameter name
   let X'(i:Drums M S): Verse ι Unit:= ⟨(raw M i).letters,fun _=> X ((team M i).cicada) U⟩
   let a(i:Drums M S):= (X' i).opera Z l ()
   have he : S.IsKernel R.beta G:= S.isKernel (funds_branch H.laws.intake.ready) _
   have hp (p:Drums M S):Integrable (raw M p).utter (prior G f):= ((team M p).sells H.laws.intake.cap).1.integrable _
   have ht: (fun t v=> S.push R.beta (buy M (l' t v) S) U)=∑ i:Drums M S,a i:=by
     ext t V; simp_rw [StepData.push,buy,sale, smul_eq_mul, Finset.sum_apply]; rw [show (fun x:Config G f=>_)=fun u=>∑ p:Drums M S, (∏ j∈p.val,l' t V j)*(S.density R.beta u U * (team M p).cicada u) from ?_]
     swap; · ext v; rw [Finset.mul_sum]; exact sum_congr rfl fun i _=>mul_left_comm ..
     rw [integral_finsetSum]; refine sum_congr rfl fun i _=>?_ ; rw [integral_const_mul]; rfl
     intro i _; exact (StepData.push_slice he U ((raw M i).utter) (hp i)).const_mul _
   let F(i:Drums M S):= ‖(X' i).emit l ()‖
   have h i : Switch.Paid (fun _ : Unit=> a i) (F i) := Switch.Paid.toPoint _ (Verse.earns (X' i) Z l _ (norm_nonneg _) (fun u=> by cases u; exact le_rfl)) ()
   rw [ht,summed z univ a F (fun i _=>h i)]; simp_rw [a,tones _ Z l z hZ]
   unfold StepData.push; simp_rw [Finset.smul_sum]; rw [integral_finsetSum]
   · apply Finset.sum_congr rfl; intro p _; let V':= controls Z z (raw M p).letters; let c':=(raw M p).stock l
     let f i:= (raw M p).utter i; let g i:= S.density R.beta i U*c'
     have he'(i):S.density R.beta i U • ((raw M p).paint Z l z i)=(c'*(S.density R.beta i U*f i)) • V':=by
       unfold paint; change S.density _ _ _ • ((c'*f i) • V')=_; rw [← mul_smul]; exact congr_arg (· • V') (mul_left_comm ..)
     simp_rw [he',integral_smul_const, integral_const_mul]; rfl
   intro i _; exact StepData.push_slice he U _ (((hp i).const_mul ((raw M i).stock l)).smul_const (controls Z z (raw M i).letters))

open Mallow Merge.Photo Ovens Progress.DirectedRecipe
variable {R':Rep G f} (Y:Cash W x μ L Q o C T R')(D:Match.Alliance Y H 1 0)(V:BudgetPoint)(E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ) (hx:V.threshold=Pressure.temp x) (he:V.B=radiusB x)(ha:V.supportExponent≤ a)
local notation "VB"=> Refrain.read Y D χ E t'
open Daisy
local notation "Funds'"=> Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)
local notation "WG" => wing M H χ Z l Y D
local notation "mz" => med M H χ Z l

def poem (p:H.fragrances)(U:Config G c): Poly Jm:= ∑ w:Syllable M H p,(L₀ p w).paint Z l z U
def showK (i:ℕ): Config G c→Poly Jm:=stuff (Refrain.visa Y D) (fun p U=>∑ w:Scene M H p.val,(P₀ p.val w).paint Z l z U) i

variable (hl:Plot M H l) (hp : Bikes Q L μ x a L' B j n)
local notation "zm"=> poem M H χ Z l z
local notation "PG" => showK M H χ Z l z Y D
local notation "SG" => (black VB (WG 0 ∅))
include hZ H N hl
lemma counting (p:H.fragrances)(U:Config G c): sound z (mz p U)=zm p U:=by
  unfold poem; simp_rw [← tones _ Z l z hZ]
  let f i:= (L₀ p i)
  rw [show mz p U=∑ i:Syllable M H p,(f i).opera Z l U from (by ext; simp [med, f])]
  exact summed z univ _ _ (fun i _=> Switch.Paid.toPoint _ (Verse.earns _ Z l (kronor M H l p i) ((norm_nonneg _).trans (drinks M H χ N l hl.live p i U)) (drinks M H χ N l hl.live p i)) U)
lemma F_end (i:ℕ)(U:Config G c): sound z (fun t v=>WG t v i U)= PG i U:=by
  by_cases he:i∈Set.range (Refrain.visa Y D)
  · obtain ⟨p,rfl⟩:=he; unfold showK wing shootK; simp_rw [stuffed, voyage M H χ N]; let f s:= (P₀ p.val s)
    simp_rw [← tones _ Z l z hZ];
    let a:= ∑ i:Scene M H p.val,(f i).opera Z l U
    have ht : (fun t v=> ∑ s:Scene M H p.val,(P₀ p.val s).emit (l' t v) U)=a:=by ext;simp [a];rfl
    rw [ht]
    exact summed z univ _ _ (fun i _=>Switch.Paid.toPoint _ (Verse.earns _ Z l (Bank M H l p.val i) ((norm_nonneg _).trans (camping M H χ N l hl.live _ _ U)) (camping M H χ N l hl.live _ _)) U)
  unfold wing shootK showK; simp_rw [Progress.DirectedRecipe.blank _ _ he]; change sound z (fun _ _=>0)=0; rw [const_sounds]; simp

include hx hp he ha
omit hZ in
lemma money : Motion.Pays SG V WG Funds' V.supportExponent:=by
   have h:= Paid_wing M H χ N Z l Y D V E t' hx hl hp he
   refine ⟨h.term,h.licensed,?_⟩; obtain ⟨f,hF,hB⟩:= h.bought; refine ⟨f,hF,fun i=>?_⟩
   refine budget_mono (hB i) (fun i=> ?_) (fun i=> ?_)
   · split; exact mul_nonneg ((hF _).rocket) (Real.exp_pos _).le; rfl
   split; next h=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (by positivity))) ((hF _).rocket)
   next=> exact le_rfl
lemma closed (X:Tree.Forest S.ratio)(U:Config G c):
    let L:=fun i=>zm i U; let a':= overhead (prism T x χ o.K U X) R Q.table
    let u:= fun j=> PG j U
    let K:= Photo.fronts VB u U V
    Summable L ∧ Summable K ∧ S.push R.beta f' U= (↑a':ℂ) • (GridRenewal.Rain.cyclone (∑' i,L i) *∑' i,K i):=by
   intro L'' a' u' K'
   have hh := money M H χ N Z l Y D V E t' hx he ha hl hp -- hZ false dependency
   let f p:= mz p U
   have ht (p:H.fragrances): Switch.Paid (fun _ : Unit=> f p) (lace M H l n p):= Switch.Paid.toPoint _ (Med_paid M H χ N Z l hl p) U
   have hμ:= Palette.sizes M H χ l hl hp N.balance
   let a : Ways ι:= fun x v=> ∑' p,f p x v
   have hs: HasSum L'' (sound z a):= (soundSum z _ ht hμ.2 (fun _ _ _=>rfl:∀ x∈Set.Icc (0:ℝ) 1,∀ v, ∑' p,f p x v=a x v)).congr_fun (fun i=>(counting M H χ N Z l z hZ hl _ _).symm)
   let G':Ways ι:= fun t v=> (black (SG) (WG t v)).gas V U
   have hf:HasSum K' (sound z G'):= (Photo.holds z hZ _ _ hh U).congr_fun (fun i=>?_)
   swap; · have h:(fun i=>sound z (fun t v=>WG t v i U))=u':=funext fun i=> F_end M H χ N Z l z hZ Y D hl i U; unfold K'; rw [← h]; rfl
   refine ⟨hs.summable,hf.summable,?_⟩
   have ha: Switch.Paid (fun _ : Unit=>a) (∑' i, lace M H l n i):=(issue ht hμ.2).1
   let F': Ways ι:=fun t v=> Real.exp (a t v)
   let A': Ways ι:=fun _ _=> a'
   have he' : Switch.Paid (fun _ : Unit=>F') _:= ha.exponential
   obtain ⟨b,hb,hB⟩:=Photo.tomes_budget _ _ hh
   have hG: Switch.Paid (fun _ : Unit=>G') (∑' i,b i):= (Switch.issue (fun i=> Switch.Paid.toPoint _ (hB i) U) hb).1
   have hKc : Switch.Paid (fun _: Unit=> A') ‖a'‖:= Switch.constant (fun _=>a') (norm_nonneg _) (fun _=>le_rfl)
   rw [hs.tsum_eq,hf.tsum_eq,← Switch.soundExp _ hZ ha,← Poly.product_bead,band M H Z l z hZ, ← const_sounds z a']
   change _=sound z A'*(sound z F'*_)
   rw [← mul_sounds z hZ (show Models F' _ from (he'.works ()).choose_spec) (show Models G' _ from (hG.works ()).choose_spec), ← mul_sounds z hZ (show Models A' _ from (hKc.works ()).choose_spec) (show Models (F'*G') _ from ((he'.mul hG).works ()).choose_spec)]
   apply congr_arg (mapScores Jm z); refine Switch.cong (approached.mono (fun x hx' => funext fun v=>?_))
   rw [← Mosaic.commute M H χ N Z l Y D V E t' hx hl hp X x ⟨hx'.1.le,hx'.2⟩ v]; exact mul_assoc ..
end YM.RemainderComparison.Mosaic
