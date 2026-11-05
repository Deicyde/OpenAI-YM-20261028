import YM.RemainderComparison.Valse.Gala
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Valse
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory
open AnalyticBridge.GaussianFieldAlignment Locations Channels
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Itinerary Raw Matter
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open PhysicalNext.Repeat Lotus Merge Palette Turn
open Mosaic
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {ι ι' δ : Type} {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}
    {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    {W α μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {L : Side}
    {R : Rep G f} (π : R.activities.Moves s (S.ratio.embed b)) (H : Cash W α μ L Q o C T R)
variable (M : ι→Leaf R)(N:ι'→Leaf R)(u : ι≃ι')
variable (B: Turns π M N u)
namespace Turns
local notation "D₁"=> drums π M N u B
local notation "A₁" => Match.swing H π
open Match Sleet Mosaic Blaze March Captain
variable {a b₀ c₀ q d v k' t s' : ℝ} {i j:ℕ}{χ:Chi}
variable (C': Captain H j a b₀ c₀ q d v k' t s' i χ)
include B
def prosody (p:H.fragrances) : Lyric.Syllable M H p ≃ Lyric.Syllable N H ((A₁).furrow p) := Equiv.arrowCongr (Equiv.refl _) D₁
local notation "Pʼ"=> prosody π H M N u B
lemma octave (p:H.fragrances) (w:Lyric.Syllable M H p) (j:Option (Fin p.1)): Pʼ p w j=D₁ (w j):= rfl
include C'
lemma glows (V:Config G c) (p:H.fragrances) (w:Lyric.Syllable M H p) : Lyric.cut M H χ p w (pull s b V)= Lyric.cut N H χ ((A₁).furrow p) (Pʼ p w) V:=by
   rw [← Lyric.scripted M H χ _ _ C', ← Lyric.scripted N H χ _ _ C', Lyric.cadence,Lyric.cadence,Match.weighs (A₁).bearing (A₁).sec p]; apply congr_arg; exact prod_congr rfl (fun i _=> chance π H M N u B V χ (p.2 i).val (w i))
omit C'
variable (l : ι→ℝ)(l':ι'→ℝ)(hp: ∀ i, l i=l' (u i))
include hp
lemma value (p:H.fragrances)(w:Lyric.Syllable M H p) : (etude M H χ p w).stock l=(etude N H χ ((A₁).furrow p) (Pʼ p w)).stock l':=by rw [Mosaic.pieces,Mosaic.pieces]; exact prod_congr rfl fun i _=> values u _ _ (tran π M N u B (w i)) _ _ (fun j _=>hp j)
include C'
lemma career (p:H.fragrances)(w:Lyric.Syllable M H p)(V:Config G c): (jewel M H χ p w).emit l (pull s b V)=(jewel N H χ ((A₁).furrow p) (Pʼ p w)).emit l' V:= congr_arg₂ (· * ·) (value π H M N u B l l' hp (χ:=χ) p w) (glows π H M N u B C' V p w)

def label : Staff M H ≃ Staff N H:= Equiv.sigmaCongr (A₁).furrow Pʼ -- C' include only lemmas automatically?
omit hp C'
-- K orientation on unmarked subfamily (natural book)
set_option quotPrecheck false
local notation "Kʼ"=> (A₁).editor

def spell : ∀ p:H.Chapter, Stone M H p ≃ Stone N H (Kʼ p)
 | .inl _=> D₁
 | .inr p=> Pʼ p
local notation "S'"=> spell π H M N u B
include hp C'
lemma motto (p:H.Chapter)(w:Stone M H p)(V:Config G c) : (panel M H χ p w).emit l (pull s b V) = (panel N H χ (Kʼ p) (S' p w)).emit l' V:=by
   rcases p with p|p
   · refine congr_arg₂ (· * ·) (values u _ _ (tran π M N u B w) l l' (fun i _=> hp _)) (chance π H M N u B V χ p.val w)
   exact congr_arg₂ (· * ·) (value π H M N u B l l' hp (χ:=χ) p w) (congr_arg Neg.neg (glows π H M N u B C' V p w))
omit hp C'
local notation "T₁"=> (A₁).tongs
local notation "g" x:max => Match.tallyVip Kʼ (x).fst

def size (p:H.Chainbook)(j:↥p.1) : Slots H p j≃Slots H (T₁ p) ((g p) j):= finCongr (congr_arg (·+1) (numbers Kʼ p j).symm)
local notation "N₁"=> Turns.size π H -- B? size doesn't mention B

def table (p:H.Chainbook): Scene M H p ≃ Scene N H ((A₁).tongs p):= Equiv.piCongr (g p) (fun j=> Equiv.arrowCongr (N₁ p j) (S' j.val))
local notation "Tʼ"=> table π H M N u B
lemma portion (p:H.Chainbook)(w:Scene M H p)(j:↥p.1)(k:Slots H p j): Tʼ p w ((g p) j) (N₁ p j k)=S' j.val (w j k):=by
    -- dep casts
    have hf : Tʼ p w ((g p) j)= Equiv.arrowCongr (N₁ p j) (S' j.val) (w j):= Equiv.piCongr_apply_apply ..; rw [hf]; change S' j.val (w j ((N₁ p j).symm (N₁ p j k)))= _; rw [Equiv.symm_apply_apply]
include hp C'
lemma frosts (p:H.Chainbook)(w:Scene M H p)(V:Config G c) : (parade M H χ p w).emit l (pull s b V)=(parade N H χ (T₁ p) (Tʼ p w)).emit l' V:=by
    rw [wheel,wheel]; have h : sealing H p (pull s b V)↔ sealing H (T₁ p) V:=and_congr ( (A₁).sap p) (and_congr ((A₁).splint p) ((A₁).festoon V p)) -- missing
    refine if_congr h ?_ rfl
    apply Fintype.prod_equiv (g p); intro j; rw [show (T₁ p).2 _= p.2 j from numbers Kʼ p j]; refine congr_arg (· / ((p.2 j+1).factorial:ℝ)) ?_; apply Fintype.prod_equiv (N₁ p j); intro k; rw [portion]; exact motto π H M N u B C' l l' hp j.val (w j k) V
end Turns
end YM.RemainderComparison.Valse
