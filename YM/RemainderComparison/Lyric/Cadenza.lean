import YM.RemainderComparison.Lyric.KForce

/-!
# Unseparated polynomial (before reset)

Yes extensive scalar retained in this bridge; extraction of `overhead` owned
by RG03 in choice of coordinates -- always compare relative to committed kinetic
rows. Handles all Mark.Play using switch relations, orientation via picking
forest (arbitrary) and authentic log layouts on ALL masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Daisy
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
open Height AnalyticBridge.VerifiedReset
variable {δ Gp:ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "λ₀" => mulScale ((tax G L x)⁻¹) l
local notation "F'" => Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)

open PhysicalNext.Repeat Mallow Merge.Photo Progress.DirectedRecipe
open Ovens
variable {R':Rep G f} (Y : Cash W x μ L Q o C T R') (D:Match.Alliance Y H 1 0) (V:BudgetPoint)
variable (E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ) (hx: V.threshold=Pressure.temp x)(he:V.B=radiusB x)(ha:V.supportExponent≤ a)
local notation "VB"=> Refrain.read Y D χ E t'
local notation "K₀"=> Palette.shoot M H χ (mulScale ((tax G L x)⁻¹) l) Y D

variable (hp: Premium Q L x a μ L' B j n k s J m Gp) (hl : Palette.Plot M H (mulScale ((tax G L x)⁻¹) l))

include hp hl N hx he ha in
lemma kingdom : Motion.Pays VB V K₀ F' V.supportExponent:=by
   have hh:= routine M H χ l N Y D V E t' hx he hp hl
   refine ⟨hh.term,hh.licensed,?_⟩
   obtain ⟨b,hb,hT⟩:= hh.bought; refine ⟨b,hb,fun i=> ?_⟩
   refine budget_mono (hT i) (fun i=>?_) (fun i=>?_)
   · dsimp only; split; exact mul_nonneg (hb _ |>.rocket) (Real.exp_pos _).le; rfl
   dsimp only; split
   next hf=>exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (hb _ |>.rocket)
   next=> exact le_rfl

open Marker Switch GridRenewal.Rain
variable (U:Config G c)
variable {τ:Type} [DecidableEq τ] {Jm:Census τ} (r':ι→Poly Jm)
local notation "Sg" => fun i=> (Complex.ofReal (tax G L x)) • r' i
-- Align subjects returning scores to UV weights
include hp
include N
lemma fermata (z:H.fragrances) :
     sound Sg (Palette.song M H χ λ₀ z U) = ∑ f:Syllable M H z,
        if Turns M H z f then
          ((↑(invests M H z f l*cut M H χ z f U)):ℂ) • ∏i∈page M H z f,r' i
        else 0:=by
   unfold sound; rw [mapScores_apply]; simp_rw [scripts M H χ _ N λ₀ U, Complex.ofReal_sum, Finset.sum_smul]; rw [Finset.sum_comm]; refine sum_congr rfl fun t _=> ?_
   have hx:1≤ tax G L x:= one_le_pow₀ hp.roll; have hp:0 < tax G L x:=zero_lt_one.trans_le hx
   split; next he=>
      rw [sum_eq_single (page M H z t)]
      · rw [if_pos ⟨he,rfl⟩,Finset.prod_smul,prod_const,smul_smul]; have hx : #(page M H z t)=notes M H z t:= card_biUnion he
        apply congr_arg (fun c:ℂ=> c • _); rw [Lyric.toll,← Complex.ofReal_pow,hx, ← Complex.ofReal_mul]; apply congrArg; rw [inv_pow]; field_simp
      · intro b hb hn; rw [if_neg (fun hx=>hn hx.2)]; simp
      simp
   next hh => apply Finset.sum_eq_zero; intro i hi; rw [if_neg (fun h=>hh h.1)]; simp

omit N in
lemma keyTransfer : given (S:=S) M λ₀ Jm (fun i=> (↑(tax G L x):ℂ) • r' i)= given (S:=S) M l Jm r':=by
   funext U; refine sum_congr rfl fun i _=>?_ ; unfold mulScale; rw [prod_smul,prod_const,smul_smul,prod_mul_distrib,prod_const];
   apply congr_arg (fun c:ℂ=> c • _)
   have hx:1≤ tax G L x:= one_le_pow₀ hp.roll; have he':0 < tax G L x:=zero_lt_one.trans_le hx
   rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]; apply congrArg; rw [inv_pow]; field_simp

omit N hp in
lemma codK (i:ℕ) : (∑ z:Finset ι,(↑(cod M H χ l Y D i U z):ℂ) • ∏ j∈z,r' j) = sound Sg (fun t v=> K₀ t v i U):= by
   unfold sound cod; rw [mapScores_apply]; refine sum_congr rfl fun i _=>?_ ; rw [prod_smul,prod_const,Complex.ofReal_mul,smul_smul]; rw [Complex.ofReal_pow,mul_comm ( (↑(tax G L x):ℂ)^_)]
variable (hv : ∀ i,r' i*r' i=0)

include hp hl hx he ha hv
lemma salutes (F:Tree.Forest S.ratio) :
    let Lyrics(z:H.fragrances):= ∑ w:Syllable M H z,
        if Turns M H z w then
          ((↑(invests M H z w l*cut M H χ z w U)):ℂ) • ∏i∈page M H z w,r' i else 0
    let a:= overhead (prism T x χ o.K U F) R Q.table
    let G₀:ℕ→Poly Jm:=fun i=>∑ z:Finset ι,(↑(cod M H χ l Y D i U z):ℂ) • ∏ j∈z,r' j
    let K:=fronts VB G₀ U V
    Summable Lyrics ∧ Summable K ∧
      S.push R.beta (given (S:=S) M l Jm r') U= (↑a:ℂ) •(GridRenewal.Rain.cyclone (∑' z,Lyrics z)*(∑' i,K i)):=by
  intro Sg' a' G₀ K
  let r i:= (↑(tax G L x):ℂ) • r' i
  have hr(i): r i*r i=0:=by unfold r; rw [smul_mul_smul_comm,hv,smul_zero]
  let f i(t:ℝ)(u:Finset ι):= Palette.song M H χ λ₀ i U t u
  let Z : Ways ι:= fun t p=>∑' i,f i t p
  let Y':Ways ι:=fun t p=> Real.exp (Z t p)
  let Z':Ways ι:=fun t u=> (black VB (K₀ t u)).gas V U
  have hμ: Motion.Pays VB V K₀ F' V.supportExponent:=kingdom M H χ l N Y D V E t' hx he ha hp hl
  obtain ⟨w,hb,hB⟩:= tomes_budget (VB) K₀ hμ
  have hZ: Switch.Paid (fun _:Unit=>Z') (∑' i,w i) := (Switch.issue (fun i=>show Switch.Paid _ _ from (hB i).toPoint (tomes (P:=V) VB K₀ i) U) hb).1
  have hs : ∀ i, Switch.Paid (fun _: Unit=>f i) (lace M H λ₀ n i):= fun i=>Switch.Paid.toPoint _ (Palette.fair M H χ λ₀ hl i n) U
  have hp' := (Palette.sizes M H χ λ₀ hl hp.visit N.balance).2
  have hT := soundSum r f hs hp' (fun _ _ _=> rfl : ∀ x∈Set.Icc (0:ℝ) 1,∀ v, ∑' i, f i x v= Z x v)
  have hf : HasSum Sg' (sound r Z):= hT.congr_fun (fun i=> (fermata M H χ l N hp U r' i).symm)
  have hx' : HasSum K (sound r Z') := (Photo.holds r hr (VB) K₀ hμ U).congr_fun (fun i=>congr_fun (congr_arg (fun f=> fronts (VB) f U V) (funext fun j=>codK M H χ l Y D U r' j)) i)
  let a: Ways ι := fun _ _=> a'; have ha' : Switch.Paid (fun _:Unit=>a) ‖a'‖:=Switch.constant _ (norm_nonneg _) (fun _=>le_rfl)
  have hz := (Switch.issue hs hp').1; have hE:= hz.exponential
  refine ⟨hf.summable,hx'.summable,?_⟩
  rw [hx'.tsum_eq,hf.tsum_eq,← keyTransfer M l (S:=S) hp,Photo.which M H]
  change sound r _= (↑a':ℂ) • _
  rw [show cyclone (sound r Z)= sound r Y' from (Switch.soundExp r hr hz).symm, ← Poly.product_bead, ← const_sounds r a']
  change _=sound r a*(sound r Y' * _); rw [← mul_sounds r hr (show Models Y' _ from (hE.works ()).choose_spec) (show Models Z' _ from (hZ.works ()).choose_spec),← mul_sounds r hr (show Models a _ from (ha'.works ()).choose_spec) (show Models (Y'*Z') _ from ((hE.mul hZ).works ()).choose_spec)]
  unfold sound; apply congr_arg; refine Switch.cong (Switch.approached.mono (fun t ht=>funext fun p=>?_)); have h:= Palette.chorus M H χ λ₀ hl hp.visit U F N.balance Y D V E t' hx p t ⟨ht.1.le,ht.2⟩
  have hk:= (Palette.assembled M H χ λ₀ hl hp.visit U F N.balance t ⟨ht.1.le,ht.2⟩ p).2.2
  rw [← h,← hk]; change a'*Real.exp (Z t p)*Z' t p= a'*(Y' t p*Z' t p); rw [mul_assoc]
end YM.RemainderComparison.Lyric
