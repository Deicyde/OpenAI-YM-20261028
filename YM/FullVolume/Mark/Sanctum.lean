import YM.FullVolume.Mark.Slate
import YM.FullVolume.Mark.Purse
/-!
# Orbit cast of stamped full columns, not just leading-jet transport.

Construct the abstract graph step also off the actual trajectory of columns,
keeping ACTUAL vacuum. For arbitrary graph points don't claim Sons or equality
of transmitted density values, just numerical promises on x plus regular and
forced edges. Reseated canonical graph inputs. Keeper ports throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H:History G) (N p m:ℕ)(Y:Hol G)
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "U"=> H.rep N p (m+1)
local notation "O"=> H.rep N p m
local notation "s₀"=> H.S.side (m+1) p
local notation "s₁"=> H.S.side m p
local notation "s₂"=> H.S.block m
set_option quotPrecheck false
section
variable {n:Side}{R:Rep G n}{Y:Hol G}
structure Well (R:Rep G n)(D:Desk G n)(k:ℝ): Prop where
   alongside: Along D.orient R
   paid : D.k=k
variable {X:Desk G n}{k v:ℝ}
include X
lemma granted (h:Well R X k) (Y:Hol G)(p:F.Coeff)(f:Coin F Y X) : (book p (Coin.uses f)).Format 0 Y R ∧ (book p (Coin.uses f)).remBound 0 R k ‖f‖:=by
    obtain ⟨hv,hp⟩:= Coin.wealth f; rw [←h.paid]; exact ⟨along_format _ h.alongside (formatK _ _ _ hv),along_bound _ h.alongside (boundK _ _ _ hp)⟩
lemma alongPay (h:Well R X k)(K:Keeper R.p R.activities)(P:Coefficient F n)(hp:P.Format 0 Y R)(hx:P.remBound 0 R k v): Pay F Y X (capture P K) v:=by
   have hx:= tariffs P K hp hx; have hs:= invest P K hp; exact ⟨along_format _ h.alongside.sym (formatK F _ _ hs),along_bound _ h.alongside.sym (boundK _ _ _ (h.paid.symm ▸ hx))⟩
lemma packer (K:Keeper R.p R.activities)(f:F.Coeff→ Coefficient F n)(hf:Ledger F n f)(y:F.Coeff→ℝ)(h:Well R X k)(hv:∀ i,(f i).Format 0 Y R)(hw:∀ i,(f i).remBound 0 R k (y i)):
    IsLinearMap ℂ (fun i=> Coin.saver F Y X (capture (f i) K) (alongPay h K (f i) (hv i) (hw i))) :=by
    let u i:=(f i).support; let w i:= capture (f i) K; have hu(i:F.Coeff): (w i).1= extend (tongue ((f 0).support)) (f i).regular 0:=by unfold w capture liveE; rw [hf.tags i]
    have hz:= inkL f y hf hw
    refine ⟨fun x y=> Coin.noted ?_,fun a x=> Coin.noted ?_⟩
    · rw [map_add, Coin.use_save, Coin.use_save, Coin.use_save]; change w (x+y)=_; apply Prod.ext
      · funext i; change (w (x+y)).1 i=(w x).1 i+(w y).1 i; rw [hu,hu,hu]; by_cases he:i∈ Set.range (tongue ((f 0).support)); obtain ⟨k,rfl⟩:=he; rw [(tongue _).injective.extend_apply,(tongue _).injective.extend_apply,(tongue _).injective.extend_apply,hf.reg.map_add]; rfl
        rw [extend_apply' _ _ _ he,extend_apply' _ _ _ he,extend_apply' _ _ _ he]; simp
      funext i; change stowK K (f (x+y)) i= stowK K (f x) i+stowK K (f y) i; by_cases he:i∈ range (cart K); obtain ⟨k,rfl⟩:=he; rw [stowed,stowed,stowed,hz.map_add];rfl
      rw [pit _ _ he,pit _ _ he,pit _ _ he]; simp
    rw [map_smul,Coin.use_save,Coin.use_save]; apply Prod.ext
    · funext i; change (w (a • x)).1 i=a • (w x).1 i; rw [hu,hu]; by_cases he:i∈ Set.range (tongue ((f 0).support)); obtain ⟨k,rfl⟩:=he; rw [(tongue _).injective.extend_apply,(tongue _).injective.extend_apply,hf.reg.map_smul];rfl
      rw [extend_apply' _ _ _ he,extend_apply' _ _ _ he]; simp
    funext i; change stowK K (f (a • x)) i=a • stowK K (f x) i; by_cases he:i∈range (cart K); obtain ⟨k,rfl⟩:=he; rw [stowed,stowed,hz.map_smul];rfl
    rw [pit _ _ he,pit _ _ he]; simp
end
structure Tool (F:Labels.Frame G d)(H:History G)(N p m:ℕ) where
   plate:Plate F (H.S.side (m+1) p) (H.S.side m p)
   up:Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities
   down:Keeper (H.rep N p m).p (H.rep N p m).activities
   whirl(z:Extra.Histories.Motion):(H.rep N p m).activities.Moves z.1 0
variable {B H N p m Y}
namespace Tool
variable (P:Tool F H N p m)
structure Cap (B:SectionData F)(Y:Hol G)(W: Worth)(D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(T:Heading F)(u ζ v:ℝ)(X:Set Wing):Prop where
  shines: H.Selected
  late:m<N
  dish:SoundDoor (H.levels.clock.op m p) D
  tote:X.Finite -- alias adjust
  cart:∀ i,X (.gasKey (cart (R:=H.rep N p (m+1)) P.up i))
  copies: Plate.Prints B H N p m Y P.plate T u ζ v D X
  budget: Buys H F W m u ζ
  toll:0 ≤ v
  hv:Real.sqrt (H.levels.clock.forcedAllowance (m+1)) ≤ 1
  good:B.Sound Y
variable {W:Worth}{u ζ v t:ℝ}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{T:Heading F}{X:Set Wing}
variable (h:Cap P B Y W D T u ζ v X) {S: Desk G (H.S.side (m+1) p)} (hw:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
def shot (i:F.Index) (x: File G (H.S.side (m+1) p)):= gather P.plate P.up (book (Size.axis F i) x) i
include h hw in
lemma recoil (i:F.Index)(z : Coin F Y S):let x:= Size.axis F i; let A:= book x (Coin.uses z)
   Span B H N p m Y (P.shot i (Coin.uses z)) (A.exponentialEntry 0 B U) (profile (U).activities A.forced) (x 0) D X (A.density 0 B U) (T.leads s₂ x) (ζ*(F.coeffSize (F.core x)+‖z‖)) (u*F.coeffSize (vowel F s₂ (F.core x))+ζ*‖z‖) (v+2*‖z‖):=by
    intro x A; obtain ⟨hx,hp⟩:= granted hw Y x z
    exact design B H N p m Y P.plate P.up A (X:Wing→Prop) D i h.shines h.late hx hp rfl rfl h.dish h.budget.epsilon h.copies h.hv h.cart -- defeq
section orbit
def portfolio {S:Desk G (H.S.side (m+1) p)} (R:F.Index→ Coin F Y S) (i:Tally F):= Planned.GuardedAtom.audition (P.whirl i.1) (P.shot i.2 (Coin.uses (R i.2)))
def pages {S:Desk G (H.S.side (m+1) p)} (R:F.Index→ Coin F Y S)(x:F.Coeff):= pencil (code _) (P.portfolio R) (chips F) x
variable (R:F.Index→ Coin F Y S) (hR:∀ i,‖R i‖≤ (H.levels.params (m+1)).columns*F.coeffSize (F.core (Size.axis F i)))
local notation "I"=> orbitCost F
local notation "s"=> (H.levels.params (m+1)).columns
local notation "R'"=> (H.rep N p m)
local notation "k"=> kappa H m
local notation "ε"=> ζ*(1+s)
local notation "Wc"=> u+ζ*s
local notation "B₀"=> fun v:F.Coeff=>F.coeffSize (F.core v)
local notation "W₀"=> fun v:F.Coeff=>F.coeffSize (vowel F s₂ (F.core v))
local notation "Q"=> P.pages R
include h hw
lemma portX (i:Tally F): let p:= (P.portfolio R i);p.x=Motion.patch F i.1 (P.shot i.2 (Coin.uses (R i.2))).x:=by
    intro p; have he:= (recoil P h hw i.2 (R i.2)).earns; unfold p portfolio audition;unfold Motion.patch; split<;> rfl
include hR
lemma scout (i:Tally F): let x:=Size.axis F i.2; let p:=P.portfolio R i
    p.Format 0 Y R' ∧ F.coeffSize ((Motion.patch F i.1 (P.shot i.2 (Coin.uses (R i.2))).x)- Motion.patch F i.1 (T.leads s₂ x))≤ ε*F.coeffSize (F.core x) ∧ p.remBound 0 R' k ((Wc)*(W₀ x)):=by
    intro x c; let z:=Coin.uses (R i.2); have hx:= hR i.2; have ht:s≥0:= zero_le_one.trans (H.levels.params (m+1)).columns_ge; have hz:= h.budget.epsilon; have he:= (recoil P h hw i.2 (R i.2)).earns
    obtain ⟨a,b,hq,hF⟩:= he.future; obtain ⟨hP,hA,hY,hβ⟩:= Planned.GuardedAtom.audition_receipt i.1 (P.whirl i.1) ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p)) h.good he.format hq
    refine ⟨hA,?_,hY.bound (hF.trans ?_)⟩
    · rw [← patch_sub]; refine (patch_cost ..).trans (he.leadP.trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hx) hz).trans ?_)); apply le_of_eq; unfold x; ring
    refine (add_le_add_right (mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_left (Work.G08.size_vowel F (H.S.block m) _).1 ht)) hz) _).trans (le_of_eq ?_); unfold x;ring
lemma stained (v:F.Coeff): let Z:=P.pages R v; Z.Format 0 Y R' ∧ Z.remBound 0 R' k (Wc*I* (W₀ v)) ∧ direction H W m F Z.x v (Wc*I* (W₀ v)) (s* (B₀ v)):=by
   intro Z; have he(i:Tally F):= scout P h hw R hR i; have hs:s≥0:= zero_le_one.trans (H.levels.params (m+1)).columns_ge; have hf:=h.budget.tiny; have hz:=h.budget.epsilon
   have hc: 0≤Wc:= add_nonneg (zero_le_one.trans h.budget.cost) (mul_nonneg hz hs)
   have hec:= pencil_cost (code _) (P.portfolio R) (chips F) (Real.sqrt_pos.mpr (forcedPos H.levels m)) (fun i=>⟨(he i).1,(he i).2.2⟩) v
   have hM: Z.remBound 0 R' k (Wc*I* (W₀ v)):=rem_mono hec.2 (residual_bill F s₂ Wc hc v)
   have hκ:0≤ (barunit (H.S.block m)):=by unfold barunit puffs; positivity
   refine ⟨hec.1,hM, rem_nonneg hM, mul_nonneg hs (Work.G08.size_nonneg ..),T.map,fun x=>?_,?_,?_⟩
   · have h₀:u ≤ W.K (H.levels.clock.J (m+1)):= le_trans ((le_add_of_nonneg_right (mul_nonneg hz hs)).trans (le_mul_of_one_le_right hc (orbitCost_one_le F))) h.budget.funds
     have h' := mul_le_mul_of_nonneg_right h₀ (Work.G08.size_nonneg F x)
     exact ⟨(h.copies.heading x).1.trans h',(h.copies.heading x).2.trans h',(T.core_comm x).symm⟩
   · let f i:=(P.shot i (Coin.uses (R i))).x
     have hZ: Z.x=repaint F f v:=by
         unfold Z pages; rw [pencil_x]; exact Finset.sum_congr rfl (fun i _=> congr_arg (chips F v i • ·) (portX P h hw R i))
     rw [hZ]; refine (budgets_orbit F (H.S.block m) T f v ε (mul_nonneg hz (add_nonneg zero_le_one hs)) (fun i=> (he i).2.1)).trans ?_
     exact (mul_le_mul_of_nonneg_right hf (Work.G08.size_nonneg F _)).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hs (Work.G08.size_nonneg F _))) hκ)
   rw [Work.G08.core_vowel]; exact (mul_le_mul_of_nonneg_right h.budget.funds (Work.G08.size_nonneg F _)).trans (le_add_of_nonneg_right (mul_nonneg hκ (mul_nonneg hs (Work.G08.size_nonneg F _))))
end orbit
end Tool
end YM.MergeProof.Matric
