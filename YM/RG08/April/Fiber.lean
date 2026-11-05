import YM.RG08.April.Chest
/-! # Tar lane & paid graph credentials interface. Consumer of `Sideshow.harbor` loop.
Wage stage receipts; no analytic input assumptions in solver. Suppliers separate. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.April
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Lattice Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow
open scoped Classical Matrix BigOperators PowerSeries Topology
variable {X Z:Type}{G:Gauge}{D d p l e n k r:ℕ}{σ δ:ℝ}
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover
variable (F:Labels.Frame G d)(W:Rate.Stair X)
local notation "I₀"=> Accent F
local notation "M₀"=>Playbook F
local notation "S₀"=>Bouquet F
local notation "V₀"=>Haven W
local notation "R₀"=>Mason.Run W
local notation "D0"=> Mason.kiosk W
local notation "D1"=> Mason.turnstile W
abbrev old (j:R₀):= Mason.Pier.low j
abbrev past (j:R₀):= Mason.Pier.high j
structure Housing (F:Labels.Frame G d)(W:Rate.Stair X) (D k:ℕ) where
 strip: Haven W→ℝ
 stand: ∀ i,0<strip i
 S : Haven W→Bouquet F
 S': Haven W→Bouquet F
 P : Mason.Run W→ Playbook F
 P': Mason.Run W→ Playbook F
 wish:∀ i:Haven W,Silo F D k (stand i) (S i)∧ Silo F D k (stand i) (S' i)
 score:∀ i:Mason.Run W,Cloth (P i)∧Cloth (P' i)
 debt: Mason.Run W→ℝ
 tiny:(Mason.turnstile W).cheap debt
 never:∀ i,0<debt i
 afford:∀ (e l n:ℕ),e≤k→l≤d→n≤l+e→∃ A J:Mason.Run W→ℝ,(Mason.turnstile W).Good A∧(Mason.turnstile W).Good J∧∀ x:Mason.Run W,1≤A x∧1≤J x∧(A x)^2≤ W.length x.x x.m∧∀ {B δ B0 B1 T:ℝ}, debt x ≤ δ→
  Stamps F D e n l B δ (stand (past W x)) (stand (old W x)) (S (past W x)) (S' (past W x)) (S (old W x)) (S' (old W x)) (P x) (P' x)→0≤B0→0≤B1→0≤T→(∀ i∈Sideshow.booth F l,Sings (stance (Loc G 1)) D (stand (past W x)) (S (past W x) i e n) B0 ∧ Sings (stance (Loc G 1)) D (stand (past W x)) (S' (past W x) i e n) B1∧ Sings (stance (Loc G 1)) D (stand (past W x)) (S (past W x) i e n-S' (past W x) i e n) T) →
  Replies F D e n l (A x) (J x*B^2) (J x*(B+B1)^4) B0 B1 (W.length x.x x.m) δ T (stand (old W x)) (S (old W x)) (S' (old W x)) (P x) (P' x)
 vault (e n:ℕ)(_he:e≤k):∃ p:Haven W→ℝ,(Mason.kiosk W).Good p∧∀ i:Haven W,i.m=W.top i.x→∀ j:(Accent F),Sings (stance (Loc G 1)) D (stand i) (S i j e n) (p i)∧ Sings (stance (Loc G 1)) D (stand i) (S' i j e n) (p i)

variable (H:Housing F W D k)
def known(e l n:ℕ):Prop:=∀ i:I₀,octave i=l → Blue D0 D H.strip H.stand (fun j=>H.S j i e n) (fun j=>H.S' j i e n)
def able(e l n:ℕ):Prop:=∀ i t:I₀,octave i=l → n≤ octave t → Oil D1 (fun j=>tap e (H.P j t i)) (fun j=>tap e (H.P' j t i))

def Uptick (e l n a b r:ℕ):Prop:=a<e ∨ a=e∧(b<l ∨ b=l∧n<r)
structure Festival (e l n:ℕ):Prop where
 worth:∀ a b r,a≤k→b≤d→ r ≤b+a→ Uptick e l n a b r→ known F W H a b r
 tape:∀ a b r,a≤k→b≤d→ r ≤b+a→ Uptick e l n a b r→ able F W H a b r

lemma budget (hh:W.Admits)(he:Festival F W H e l n)(hf:e≤k)(_h0:l≤d):∃ B δ:Mason.Run W→ℝ,(D1).Good B ∧ (D1).cheap δ ∧∀ j:Mason.Run W,H.debt j ≤ δ j ∧
  Stamps F D e n l (B j) (δ j) (H.stand (past W j)) (H.stand (old W j)) (H.S (past W j)) (H.S' (past W j)) (H.S (old W j)) (H.S' (old W j)) (H.P j) (H.P' j):=by
 let I:= I₀ × Fin (e+1) × Fin (d+e+1)
 let g(i:I):=i.2.2.val;let f(i:I):=i.2.1.val;let v(i:I):Prop:=g i ≤ octave i.1+f i ∧ Uptick e l n (f i) (octave i.1) (g i)
 let u (P:Haven W→Bouquet F)(i:I)(x:Haven W):=if v i then P x i.1 (f i) (g i) else 0
 have hy(i:I):Blue D0 D H.strip H.stand (u H.S i) (u H.S' i):=by
    unfold u;split_ifs with hc
    · exact he.worth _ _ _ (by have :=i.2.1.isLt;unfold f;omega) (octave_le _) hc.1 hc.2 _ rfl
    exact blue_zero
 obtain ⟨a,r,ha,hA,hr,h⟩:=farmBlue hy
 let T:=I₀ × I₀ × Fin e
 have ht(i:T):=he.tape i.2.2.val (octave i.1) 0 (by have :=i.2.2.isLt;omega) (octave_le _) (by omega) (Or.inl i.2.2.isLt) i.1 i.2.1 rfl (by omega)
 obtain ⟨c,g',hc,hg,h'⟩:=farmOil ht
 let B(j:R₀):= a (past W j)+a (old W j)+c j; let δ(j:R₀):= r (past W j)+r (old W j)+g' j+H.debt j
 let P:=highString hh
 have hβ:(D1).Good B:=(D1).hear _ _ ((D1).hear _ _ (P.golf _ ha) (lowString.golf _ ha)) hc
 have hδ:(D1).cheap δ:=(D1).lasts _ _ ((D1).lasts _ _ ((D1).lasts _ _ (P.glow _ hr) (lowString.glow _ hr)) hg) H.tiny
 refine ⟨B,δ,hβ,hδ,fun j=>?_⟩
 have hr'(i:V₀):0 ≤ r i:=tiny D0 hr i; have hc':0≤c j:=(D1).safe _ hc j; have hg':0≤g' j:=tiny D1 hg j; have hD:=H.never j
 have h1:a (past W j)≤ B j:=by unfold B;linarith only [hA (old W j),hc']
 have h2:a (old W j)≤ B j:=by unfold B;linarith only [hA (past W j),hc']
 have hdb:H.debt j≤δ j:=by unfold δ;linarith only [hr' (old W j),hr' (past W j),hg']
 have hh₁:r (past W j)≤δ j:=by unfold δ;linarith only [hr' (old W j),hg',hD]
 have hh₂:r (old W j)≤δ j:=by unfold δ;linarith only [hr' (past W j),hg',hD]
 have hh₃:1≤ B j:=(hA (past W j)).trans h1;have hh₄:0≤δ j:=(D1).safe _ ((D1).nope _ hδ) j
 have χ:δ j≤ B j*δ j:=le_mul_of_one_le_left hh₄ hh₃
 have hx(i:I₀)(b r':ℕ)(hi:r'≤octave i+b)(hs:Uptick e l n b (octave i) r') (p:V₀)(hL:r p≤δ j)(hR:a p≤ B j):
    Dyad Δ D (H.stand p) (B j) (δ j) (H.S p i b r') (H.S' p i b r'):=by
    let k:I:=(i,⟨b,by unfold Uptick at hs;omega⟩,⟨r',by have :=octave_le i;unfold Uptick at hs;omega⟩)
    obtain ⟨hN,hN',hd⟩:=h k p
    have hc: v k:=⟨hi,hs⟩; have H1(S):u S k p=S p i b r':=if_pos hc
    rw [H1] at hN hN';rw [H1,H1] at hd
    exact ⟨zero_le_one.trans hh₃,hh₄,⟨(((H.wish p).1.unbound i).inlet.price _ _).1,(((H.wish p).2.unbound i).inlet.price _ _).1⟩,hN.mono le_rfl le_rfl (fun _=>le_rfl) hR,hN'.mono le_rfl le_rfl (fun _=>le_rfl) hR,hd.mono le_rfl le_rfl (fun _=>le_rfl) (hL.trans χ)⟩
 refine ⟨hdb,hh₃,fun i m k h' hz he=>hx i m k (h'.symm ▸ hz) (by unfold Uptick;omega) _ hh₁ h1, fun i m k hi=>?_,?_⟩
 · by_cases hK:k≤octave i+m; · exact hx i m k hK (by unfold Uptick;omega) _ hh₂ h2
   rw [show H.S (old W j) i m k=0 from Classical.not_not.mp (fun hy=>hK (((H.wish _).1.unbound _).inlet.lit _ _ hy)),show H.S' (old W j) i m k=0 from Classical.not_not.mp fun hy=> hK (((H.wish _).2.unbound _).inlet.lit _ _ hy)]
   exact (Dyad.zero hh₄).mono (zero_le_one.trans hh₃)
 intro a' i t ht
 obtain ⟨hu,hv,hG⟩:=h' (i,t,⟨a',ht⟩) j
 have h3:c j≤ B j:=by unfold B;linarith only [hA (past W j),hA (old W j)]
 have h4:g' j≤ δ j:=by unfold δ;linarith only [hr' (past W j),hr' (old W j),hD]
 exact ⟨hu.trans h3,hv.trans h3,hG.trans (h4.trans χ)⟩
end YM.RG08.April
