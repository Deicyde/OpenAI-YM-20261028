import YM.RemainderComparison.Mosaic.Crown
import YM.RemainderComparison.Mosaic.States

/-!
# Joint evaluations under Switch calculus
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
local notation "l'"=> wave Z l

-- refund Plot
lemma lessen (hi : Palette.Plot M H l) (p:ι→ℝ)(hr:∀ i,0≤p i)(hp: ∀ i,p i≤l i):Plot M H p:=by
   have hv (i: ConnectedActivityE6.Alphabet c f): 0 ≤ Palette.pitch M H p i := add_nonneg (H.armed.holds i) (sum_nonneg fun j _=> by split; exact mul_nonneg (hr _) ((M _).profit); exact le_rfl)
   have hh i : Palette.pitch M H p i ≤ Palette.pitch M H l i:= add_le_add_right (sum_le_sum fun i _=> by split_ifs; exact mul_le_mul_of_nonneg_right (hp _) ((M _).profit); rfl) _
   refine ⟨⟨hi.pays.packetBound,hv,hi.pays.extra,fun j=>budget_mono (hi.pays.pays j) (fun i=>?_) (fun i=>?_)⟩,hr⟩
   · split; exact mul_nonneg (mul_nonneg (hv _) (Real.exp_pos _).le) (Real.exp_pos _).le; exact le_rfl
   split; next=> exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hh _) (Real.exp_pos _).le) (Real.exp_pos _).le
   next=> exact le_rfl
lemma subsidizes (t:ℝ) (ht:t∈Set.Icc (0:ℝ) 1) (p:Finset ι)(h:Plot M H l):Plot M H (l' t p):=by
   have hp i: roll Z i t p∈Set.Icc (0:ℝ) 1:=by
     unfold roll; split; unfold Switch.click; simp_rw [card_singleton,pow_one, mul_one]; split; exact ht; exact ⟨le_rfl,zero_le_one⟩
     exact ⟨zero_le_one,le_rfl⟩
   apply lessen M H l h; · exact fun i=>mul_nonneg (h.live _) (hp i|>.1)
   exact fun i=> mul_le_of_le_one_right (h.live _) (hp i|>.2)

open Mallow Merge.Photo Ovens Progress.DirectedRecipe
variable {R':Rep G f} (Y:Cash W x μ L Q o C T R')(D:Match.Alliance Y H 1 0)(V:BudgetPoint)(E:ℕ→RegularAddress c)(t':ℕ→ Config G c→ℝ) (hx:V.threshold=Pressure.temp x) (he:V.B=radiusB x)
local notation "VB"=> Refrain.read Y D χ E t'
open Daisy
local notation "F'"=> Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)

def med (p:H.fragrances)(U:Config G c):Switch.Ways ι:=fun t u=> ∑ w:Syllable M H p,(L₀ p w).opera Z l U t u

def wing (t:ℝ)(p:Finset ι): Code G c := shootK M H χ Y D (l' t p)
local notation "WG" => wing M H χ Z l Y D
local notation "SG" => (black VB (WG 0 ∅))
local notation "mz" => med M H χ Z l
variable (hl:Plot M H l) (hp : Bikes Q L μ x a L' B j n)
include N hl hp hx
omit hx hp in
lemma Med_paid (p:H.fragrances): Switch.Paid (mz p) (lace M H l n p):=by
   have hh (w:Syllable M H p) : Switch.Paid ((L₀ p w).opera Z l) (kronor M H l p w) := Verse.earns (L₀ p w) Z l _ ((norm_nonneg _).trans (drinks M H χ N l hl.live p w 1)) (drinks M H χ N l hl.live p w)
   rw [show mz p=∑ w:Syllable M H p,(L₀ p w).opera Z l from (by ext; unfold med; simp only [Finset.sum_apply])]; exact (Switch.Paid.sum _ _ _ fun i _=>hh i).weaken (tickets M H n χ l hl.live p)
lemma Paid_wing (hz:V.B=sx) : Motion.Pays SG V WG F' a:=by
   constructor
   · intro p; change Palette.shootK _ _ _ _ _ _ = Palette.shootK _ _ _ _ _ _; apply congr_arg; ext i; unfold Verse.wave roll; split; unfold Switch.click; simp
     rfl
   · intro t z ht; exact Palette.earned M H χ Y D V E t' hx _
   let d:= Refrain.visa Y D; let a(p:Refrain.Leaf H) (W:Config G c) (t:ℝ)(v:Finset ι):= WG t v (d p) W
   let b (p:Refrain.Leaf H):= bold M H l n p.val
   have hb p : Switch.Paid (a p) (b p):= by
      let f (i:Scene M H (p:Refrain.Leaf H).val):=(P₀ p.val i)
      let F:= ∑ i:Scene M H p.val,(f i).opera Z l
      have he w U:= camping M H χ N l hl.live p.val w U
      have hpP : Switch.Paid F (∑ i:Scene M H p.val, Bank M H l p.val i):= Switch.Paid.sum univ _ _ (fun i _=> Verse.earns _ Z l _ ((norm_nonneg _).trans (he i 1)) (he i))
      refine Switch.Paid.congr (hpP.weaken (paradise M H χ N l hl.live p.val)) (fun u t ht=>?_); ext v; unfold F f a d wing Palette.shootK; simp_rw [stuffed,Finset.sum_apply]; exact (voyage M H χ N (l' t v) p.val u).symm
   refine ⟨stuff d b,fun i=> ?_,fun p=> ?_⟩
   · by_cases he:i∈Set.range d
     · obtain ⟨y,rfl⟩:=he; rw [stuffed]; exact hb y
     have ht t (u:Finset ι): WG t u i=0:=by unfold wing Palette.shootK; rw [Progress.DirectedRecipe.blank _ _ he]
     simp_rw [ht,blank _ _ he]; exact Switch.paidZero (U:=Config G c) (ι:=ι)
   have ht (i:ℕ): ((SG).forced i).support=((VB).forced i).support:=rfl
   refine transfer_budget d (fun z=> ?_) (fun i h=>?_) (budget_pull (fun i:Refrain.Leaf H=>i.val) Subtype.val_injective (bright M H χ l hl hp N.balance p))
   · dsimp only; simp_rw [ht,show ((VB).forced (d z)).support= _ from (Refrain.admitted Y D z).1,hz,stuffed]; rfl
   rw [blank _ _ h]; split; rw [zero_mul]; rfl

lemma commute (X: Tree.Forest S.ratio)(t:ℝ)(ht:t∈Set.Icc (0:ℝ) 1)(p:Finset ι)(U:Config G c):
   overhead (prism T x χ o.K U X) R Q.table * Real.exp (∑' z,mz z U t p) * (black (VB) (WG t p)).gas V U= S.push R.beta (Palette.buy M (l' t p) S) U:=by
     let w:=l' t p; let Z':=univ (α:=ι); have he : Palette.ways w 1 Z'=w:=by ext;simp [Palette.ways,Z']
     have hh:=subsidizes M H Z l t ht p hl
     have hv := Palette.assembled M H χ w hh hp U X N.balance 1 ⟨zero_le_one,le_rfl⟩ Z'
     have hk := Palette.chorus M H χ w hh hp U X N.balance Y D V E t' hx Z' 1 ⟨zero_le_one,le_rfl⟩; unfold Palette.shoot at hk; rw [he] at hv hk
     rw [← hv.2.2] at hk;
     simp_rw [show ∀ z, mz z U t p= H.trainedMill (Palette.color M H χ U w) z from fun z=>(canon M H χ N w z U).symm]; exact hk
end YM.RemainderComparison.Mosaic
