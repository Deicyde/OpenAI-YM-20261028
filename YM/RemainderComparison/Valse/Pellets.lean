import YM.RemainderComparison.Valse.Stage
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
    {R : Rep G f} (H : Cash W α μ L Q o C T R)
open Match Sleet Mosaic Blaze March Captain Typeface Lyric Lotus
variable {α' : Type*}(M:ι→Portrait R α')(a b' : α')(χ: Chi) (u: Set ι)
-- fights. Complement embedding.
variable (v : ℝ)(l:ι→ ℝ)
local notation "N₁" => Valse.start u
local notation "Xv" => Typeface.brand M a
local notation "Yv" => Typeface.brand M b'
local notation "S₀"=> Lobby.night (Creek.theater H χ M a l u v) u
local notation "P₁"=> Xv ∘ (start u)
local notation "Ω₁"=> Valse.stage H M a u
-- condition, simultaneous Move.Auth.R.C output variant
open Flues
local notation "Lt"=> Muse.sits u l v
set_option quotPrecheck false
local notation "Ly"=> Lt ∘ N₁
-- unused outside FUNNEL.MARK. Projection law.
variable {R':Rep G f}(H':Cash W α μ L Q o C T R')(D:Match.Alliance H' H 1 0)(f₁:ℕ→RegularAddress c) (f₂:ℕ→ Config G c→ℝ)
variable {n:ℕ} (U : Muse.Pad H n χ)
variable [Countable ι]
local notation "Dʼ"=> Flues.kettle H χ M a l u v H' D f₁ f₂
local notation "K₀"=> Flues.Elbow H M a
local notation "Fʼ"=> Flues.funnel H M a H' D
open Refrain Progress.DirectedRecipe
abbrev Unmark:= Flues.Elbow H (M ∘ N₁) a
local notation "Q₁"=> Unmark H M a u
-- naturally restricted spectrum

def limbs : Unmark H M a u ↪ Elbow H M a:= Embedding.sigmaMap (Embedding.refl _) (fun p=> Script.queue Xv H (N₁) p.val)
local notation "Vʼ"=> Valse.limbs H M a u
lemma choices (p:K₀) : p∈ Set.range (Valse.limbs H M a u)↔ Verse.load u ((Dʼ).score (Fʼ p))=0:=by
    unfold Flues.kettle; dsimp only; rw [stuffed]; obtain ⟨p,k⟩:=p
    constructor
    · rintro ⟨⟨r,v⟩,h⟩; rw [← h]; exact (Valse.gathering H χ u Xv r.val (Script.queue Xv H (N₁) r.val v)).1 ⟨v,rfl⟩
    intro ht; obtain ⟨z,rfl⟩:=(Valse.gathering H χ u Xv p.val k).2 ht; exact ⟨⟨p,z⟩,rfl⟩

variable (hp: Valse.Colorborne (S:=S) M a u l)
omit [Countable ι] in
lemma paraSign {ι':Type}{M N:ι'→ Lotus.Leaf R} (h:M=N) (i:H.Chainbook)(w:Mosaic.Scene M H i)(v:Mosaic.Scene N H i)(he:HEq w v): Mosaic.parade M H χ i w=Mosaic.parade N H χ i v:=by subst_vars; rfl
include hp
lemma marquee (p:Q₁) : (Dʼ).glow b' (Fʼ (Vʼ p))=(parade P₁ H χ p.fst.val p.snd).emit Ly:=by
    unfold Flues.kettle; dsimp only; rw [stuffed]
    let f:=fun v:Verse _ (Config G c)=>v.emit Ly
    have hh : P₁= (Yv ∘ N₁):=funext (Valse.rigid M a b' u l hp)
    change (Mosaic.parade Yv H χ p.fst.val (Script.queue Yv H N₁ p.fst.val p.snd)).emit Lt=_
    rw [show Mosaic.parade _ _ _ _ _= _ from Script.parade Yv H χ (N₁) p.fst.val p.snd,Script.alive]; exact congr_arg f (paraSign H χ hh.symm p.fst.val p.snd p.snd (HEq.refl p.snd))
namespace Oxide
-- rotation of labels and all amounts.K descriptors
variable (π:R.activities.Moves s (S.ratio.embed b))(g:Equiv.Perm (↑(uᶜ)))(B : Valse.Turns π ((Typeface.brand M a)∘ (Valse.start u)) ((Typeface.brand M a)∘ (Valse.start u)) g)
variable (hK : ∀ i,l (Valse.start u i)=l (Valse.start u (g i)))
def sheen : Equiv.Perm (Q₁):= Equiv.sigmaCongr (Refrain.gate H (Match.swing H π)) (fun i=> Valse.Turns.table π H _ _ _ B i.val)
local notation "Ψ"=> Oxide.sheen H M a u π g B
include hK U
lemma vaporized (p:Q₁)(V:Config G c) : (Dʼ).glow b' (Fʼ (Vʼ p)) (pull s b V)=(Dʼ).glow a (Fʼ (Vʼ (Ψ p))) V:=by
    rw [Valse.marquee H M a b' χ u v l H' D f₁ f₂ hp p,Valse.marquee H M a a χ u v l H' D f₁ f₂ hp (Ψ p)]
    have ht : ∀ i, Ly i=Ly (g i):=by
       intro i; unfold Muse.sits Verse.marked; dsimp only [Function.comp_apply,Pi.mul_apply]; rw [if_pos (show N₁ i ∈uᶜ from i.prop),if_pos (show N₁ (g i)∈uᶜ from (g i).prop), hK i]
    exact Valse.Turns.frosts π H _ _ _ B (U.S.N) Ly Ly ht p.fst.val p.snd V
omit hp U hK
lemma labeled (p:Q₁) : (Dʼ).more (Fʼ (Vʼ p))= Refrain.cannon H p.fst :=by
    have hh:=Refrain.admitted H' D p.fst
    have he : ∀ (P Q : ForcedAddress G c),P.support=Q.support→P.inventory=Q.inventory→P.extraTest=Q.extraTest→ P=Q:=by rintro ⟨i,j,k,l,m⟩ ⟨s,t,u,x,q⟩ h hx hk; subst_vars; rfl
    unfold kettle; dsimp only; rw [stuffed]; change Refrain.reserve H' (Refrain.badge H' (Refrain.visa H' D p.fst))= _
    refine he _ _ hh.1 hh.2 ?_; rw [Refrain.visited]; rfl
lemma turned (p:Q₁) : let z':= (Dʼ).more (Fʼ (Vʼ p)); let z'':= (Dʼ).more (Fʼ (Vʼ (Ψ p))); z''.support=z'.support.image (affine s b) ∧ z''.inventory=z'.inventory.image (affine s b)∧∀ V,z''.extraTest V ↔ z'.extraTest (pull s b V):=by
    intro x y; unfold x y; rw [labeled,labeled]; have hh:= Refrain.stem H (Match.swing H π) p.fst; exact ⟨hh.1,hh.2,fun V=> Iff.rfl⟩
end Oxide
end YM.RemainderComparison.Valse
