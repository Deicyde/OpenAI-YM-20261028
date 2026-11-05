import YM.RemainderComparison.Valse.Ink
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

structure Colorborne (l:ι→ℝ): Prop where
   -- Purely real insert estimates
   icicle : ∀ i∈ uᶜ, ∀ b:α', (Typeface.brand M b i).ingredient=(Typeface.brand M a i).ingredient
   orientation : ∀ (s:Signed)(b:Site c),∃ (π:R.activities.Moves s (S.ratio.embed b)) (t:Equiv.Perm (↥(uᶜ))),
       Valse.Turns π ((Typeface.brand M a)∘(start u)) ((Typeface.brand M a)∘(start u)) t∧∀ i,l (start u i)=l (start u (t i))

variable (hp: Colorborne (S:=S) M a u l)
-- always on unmarked.R.Vac
include H
lemma ready : Colorborne (S:=S) M a Set.univ l:=by
    constructor
    · exact fun i hi=> False.elim (hi trivial)
    intro s b; obtain ⟨π⟩:= H.laws.intake.cap.labels.moves s (S.ratio.embed b); exact ⟨π,Equiv.refl _,⟨fun i=>False.elim (i.prop trivial),fun i=> False.elim (i.prop trivial)⟩, fun i=>rfl⟩
omit H
include hp
lemma rigid (i:↑(uᶜ)) : P₁ i=(Yv ∘ (N₁)) i:=by
   have h:∀ (a b:Leaf R),a.turn=b.turn→a.ingredient=b.ingredient→a.weight=b.weight→ a=b:=by rintro ⟨u,v,w,a,b,c,d,e,h⟩ ⟨x,y,z,r,s,t,v1,h1,h2⟩ hu hx ht; subst_vars; rfl
   exact h _ _ rfl (hp.icicle i.val i.prop b').symm rfl
-- Lift same even across type-dependent casts.Words.
include H
omit hp
section
open Muse
variable (P': BudgetPoint)
local notation "Lʼ"=> (Muse.sits u l v)
local notation "Ly" => Lʼ ∘ N₁
local notation "G₀"=> Creek.theater H χ M a l u v
local notation "T₀"=> Staff P₁ H
lemma tipForge {ι:Type}{M N:ι→Leaf R} (h:M=N) (i:H.fragrances) (w:Lyric.Syllable M H i)(p:Lyric.Syllable N H i) (he:HEq w p): jewel M H χ i w=jewel N H χ i p:= by subst_vars; rfl
lemma summit (i:Staff Xv H) (U:Config G c)(hP:P'.threshold=Pressure.temp α) : (G₀).wet P' b' i U= (jewel Yv H χ i.1 i.2).emit Lʼ U:=by
    unfold WickReps.Manor.wet; rw [if_neg (show ¬ (G₀).total i from id), Creek.point,hP]; unfold jewel Verse.emit
    by_cases h: Healthy (Pressure.temp α) (Sleet.Base Xv H i) U
    · rw [masked_eq _ _ _ _ h]; change _ = _ * Lyric.cut _ _ _ _ _ U; rw [Lyric.cut,masked_eq _ _ _ _ h]; rfl
    rw [masked_ne _ _ _ _ h]; change 0= _ * Lyric.cut _ _ _ _ _ U; rw [Lyric.cut,masked_ne _ _ _ _ h,mul_zero]
-- unrestricted Beams sym carried.
include hp
lemma target (i:T₀)(U:Config G c)(hP:P'.threshold=Pressure.temp α) : (G₀).wet P' b' (Ω₁ i) U=(jewel P₁ H χ i.1 i.2).emit Ly U:=by
    rw [summit H M a b' χ u v l P' _ U hP];
    -- dependent type.Two definally reduce
    have he: P₁= Yv ∘ N₁ :=funext (rigid M a b' u l hp)
    rw [show jewel Yv H χ (Ω₁ i).fst (Ω₁ i).snd=_ from Script.poster Yv H χ (N₁) i.fst i.snd, Script.alive]
    obtain ⟨p,w⟩:=i
    dsimp only
    exact congr_arg (fun v : Verse _ (Config G c)=> v.emit Ly U) (tipForge H χ he.symm p _ w (HEq.refl w))
local notation "Ω₂"=> Creek.Academy H χ M a l u v
variable {C₀ D E I B A e k w : ℝ}{s' r n : ℕ}
variable (Q' : Muse.Pad H r χ) (hP: P'.threshold=Pressure.temp α)
-- equality any load.pℕ. mask exact.
local notation "N"=> Lobby.night (Lobby.peel (Creek.theater H χ M a l u v) (Creek.Academy H χ M a l u v n)) u
local notation "Fʼ"=> Lobby.peel G₀ (Ω₂ n)
def quota (n:ℕ) : Staff P₁ H ≃ (↑(Lobby.night (Lobby.peel (Creek.theater H χ M a l u v) (Creek.Academy H χ M a l u v n)) u)):=by
   let f : Staff P₁ H→ ↑(Lobby.night (Lobby.peel (Creek.theater H χ M a l u v) (Creek.Academy H χ M a l u v n)) u):= fun i=> ⟨⟨Ω₁ i,Valse.lights H M a χ u v l i n⟩, (Valse.from_alley H M a χ u v l _).2 ⟨i,rfl⟩⟩
   refine Equiv.ofBijective f ⟨fun i j he=> (Ω₁).injective (congr_arg (fun ζ=>ζ.val.val) he),?_⟩
   rintro i; obtain ⟨j,h⟩:=(Valse.from_alley H M a χ u v l i.val.val).1 (show i.val.val∈ S₀ from i.prop); exact ⟨j,Subtype.ext (Subtype.ext h)⟩
local notation "Qʼ"=> Valse.quota H M a χ u v l n

def west (n:ℕ)(b : α')(U:Config G c):= ∑' i:↑(Lobby.night (Lobby.peel (Creek.theater H χ M a l u v) (Creek.Academy H χ M a l u v n)) u), (Lobby.peel (Creek.theater H χ M a l u v) (Creek.Academy H χ M a l u v n)).wet P' b i.val U
local notation "W₀"=> Valse.west H M a χ u v l P' n
include Q' hP
lemma swirling (n:ℕ)(s:Signed)(b:Site c)(V:Config G c) : Valse.west H M a χ u v l P' n b' (pull s b V)= Valse.west H M a χ u v l P' n a V:=by
    obtain ⟨π,g,h,hK⟩:=hp.orientation s b
    let e:= Valse.quota H M a χ u v l n
    let f V a' (i:T₀):= (Mosaic.jewel ((Typeface.brand M a')∘ N₁) H χ i.1 i.2).emit Ly V
    have hv a' (V':Config G c) : west H M a χ u v l P' n a' V'=∑' i: T₀,f V' a i:= (e.tsum_eq _).symm.trans (tsum_congr fun i=> target H M a a' χ u v l hp P' i V' hP)
    rw [hv,hv]; let g':= Valse.Turns.label π H _ _ _ h
    have ht : ∀ i, Ly i=Ly (g i):=by
       intro i; unfold sits Verse.marked; dsimp only [Function.comp_apply,Pi.mul_apply]; rw [if_pos (show N₁ i ∈uᶜ from i.prop),if_pos (show N₁ (g i)∈uᶜ from (g i).prop), hK i]
    have he i: f (pull s b V) a i=f V a (g' i):= Valse.Turns.career π H _ _ _ h (Q'.S.N) Ly Ly ht i.fst i.snd V
    simp_rw [he]; exact g'.tsum_eq _
end
end YM.RemainderComparison.Valse
