import YM.MergeProof.Accord
import YM.MergeProof.Velvet

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent PhysicalNext.Repeat.Lotus Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{d:ℕ}(H:History G) (A:Hol G){F:Labels.Frame G d}(T:SectionData F)
   (W:Bid.Worth)(ζ u ψ:ℕ→ℝ)(t:ℝ)(i k N p:ℕ) (M:Extra.Histories.Music F H N p)
set_option quotPrecheck false
local notation "H!"=> H.levels
local notation "P"=> H.levels.budget
local notation "Γ"=> (fun m=>(H.levels.params m).columns)
local notation "R"=> H.rep N p
local notation "Gx"=> M.tone
local notation "n!"=> H.S.side N p
local notation "X"=> alto H
variable (V:F.Coeff)(a:Motion)(o:∀ m:ℕ, Site (H.S.side m p))(w:ℕ→ℝ)
   (f:∀ m:ℕ,Config G (H.S.side m p)→ℂ)(g:∀ m:ℕ,ℕ → Config G (H.S.side m p)→ℂ)(b:Config G (H.S.side N p)→ℂ)(D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
open Relay
variable (Z:∀ i:ℕ,Coefficient F (H.S.side i p))(φ:ℕ→ℝ)
def liftF (m:ℕ):Config G (H.S.side m p)→ℂ:= radiant (alto H m d) a (o m) ((Z m).exponentialEntry 0 T (R m))
def liftK (m:ℕ): Box (H.S.side m p)→ Config G (H.S.side m p)→ℂ:= sunny (R m) (Z m).forced a (o m) (alto H m d)
local notation "g!"=> liftK H N p a o Z
local notation "f!"=> liftF H T N p a o Z
local notation "T!"=> stepUp a (o N) b
-- generic cost from transmission story P. certify any ending. Can split labels X,A.
local notation "κ!"=> (fun i=>Real.sqrt (H.levels.clock.forcedAllowance i))
structure Yeast : Prop where
    ticks i:k ≤ i→ i ≤ N→ (Z i).Format 0 A (R i) ∧ (Z i).remBound 0 (R i) (κ! i) (φ i)
    rates m : k ≤ m→ m ≤ N → w m*‖alto H m d‖*(φ m+F.coeffSize (Z m).x) ≤ ζ m -- actually when m≤N.need
    votes m : k ≤ m→∀ hm:m<N,(Z m).density 0 T (R m)=blast H N p m d ((Z (m+1)).density 0 T (R (m+1))) ∧ ∃ Y:Set Wing,Y.Finite∧ Tale Y 0 0 (((H.S.block m).val:ℂ)^d) ((Z (m+1)).exponentialEntry 0 T (R (m+1))) (profile (R (m+1)).activities (Z (m+1)).forced) (profile (R m).activities (Z m).forced) ((Z (m+1)).x 0) (weighted H F (ψ m) (m+1) (Z (m+1)).x (φ (m+1))) (φ m) (D N p m hm)
    cream : ∃ (B:MergeProof.Response G (H.S.side N p))(t:ℝ),Attainment (R N).p 0 B t ∧ w N*(‖X N d‖*t) ≤ u N ∧ profile (R N).activities (Z N).forced=hook (R N).activities (R N).p.threshold B
    bill (U) : (Z N).density 0 T (R N) U=((H.S.a N:ℂ)^d)*((R N).eval U:ℂ) * b U
lemma baker (h:H.Selected)(he:T.Sound A)(hh:Yeast H A T ζ u ψ k N p w b D Z φ) (hk:k ≤ N)(hw:∀ m:ℕ,k ≤ m → m≤N → 0 < w m)(hp:∀ m:ℕ,k ≤ m→m<N→w (m+1) ≤ w m)
    (hQ:Fiesta H F ζ ψ k) (hO:∀ m:ℕ,k ≤ m→m<N→ o (m+1)=(H.levels.clock.op m p).ratio.embed (o m))
    (hD:∀ m:ℕ,k ≤ m →∀ hm:m<N, SoundDoor (H.levels.clock.op m p) (D N p m hm)) : ∃ g:∀ m:ℕ,ℕ → Config G (H.S.side m p)→ℂ,
        Wild H u k N p o w (f!) g (T!) D ∧ ∀ m:ℕ,k ≤ m→m≤N→profile (R m).activities (g m)= g! m:=by
   choose! g hG hd hx' using fun m:ℕ=> fun hK:k ≤ m=> fun hn:m≤N=> sparkling H A T (Z m) a (o m) (X m d) h 0 hn he (hh.ticks m hK hn|>.1) (hh.ticks m hK hn|>.2)
   refine ⟨g,⟨hd,fun U=>?_,?_,?_,?_⟩,fun m he hx=>(hG m he hx).symm⟩
   · change _ = coin (R N) (f! N) (g N) U; rw [show coin (R N) (f! N) (g N) U= _ from congr_fun (hx' N hk le_rfl) _]; change liftVac H N p N _ * Motion.scalar a _=alto H N d* Motion.scalar a _
     rw [hh.bill, show ((↑((R N).eval (pull a.1 (o N) U)):ℂ))= _ from vac_pull H N p N h le_rfl a.1 (o N) U]; let X0:ℂ:=(H.S.a N:ℂ)^d; have he:X0≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne'); simp_rw [Motion.scalar_mul]; rw [show Motion.scalar a X0=X0 from by unfold Motion.scalar X0;split_ifs <;>simp,show Motion.scalar a (liftVac H N p N U)=liftVac H N p N U from Motion.scalar_real ..,mul_assoc X0,show alto H N d=X0⁻¹ from rfl,inv_mul_cancel_left₀ he]
   · obtain ⟨π⟩:= (h.represents N p N le_rfl).good.labels.moves a.1 (o N); obtain ⟨Q,r,hP,H',hZ⟩:= hh.cream
     have hw:= rise a (o N) hP; rw [show affine a.1 (o N) 0=o N by simp [affine]] at hw
     have hy:= stack_of hw (X N d); refine ⟨(X N d) • upwards a (o N) Q,_,hy,H',?_⟩
     rw [hook_scale]; rw [hooked a (o N) π, ← hZ]; exact hG N hk le_rfl
   · intro m hm hm'; let S:= H.levels.clock.op m p; let c:= S.ratio.embed (o m); have hK:= hD m hm hm'; obtain ⟨_,s,hS,hL⟩:=hh.votes m hm hm'; let v:ℂ:=((H.S.block m).val:ℂ)^d
     let τ:= ((H.levels.clock.op m p).ratio.embed (o m)); obtain ⟨z⟩:= (h.represents N p (m+1) hm').good.labels.moves a.1 (S.ratio.embed (o m)); have hF:= hO m hm hm'
     have hL':= hL.gain hK a (o m) z (show scalar a v=v from by unfold scalar v; split <;> simp) |>.pitch (X (m+1) d) (X m d) (alto_at H m d)
     simp only [← hF, show affine a.1 (o m) 0=o m by simp [affine], show affine a.1 (o (m+1)) 0=o (m+1) by simp [affine]] at hL'
     have hx : k ≤ m+1:= hm.trans m.le_succ ; let c:ℝ:=Γ m; let d':ℝ:= orbitCost F*(ψ m+2*Γ (m+1))
     have hd : 2 ≤ d':=by unfold d'; exact le_trans (by linarith only [hQ.tap m hm,(H.levels.params (m+1)).columns_ge] : (2:ℝ) ≤ ψ m+2*Γ (m+1)) (le_mul_of_one_le_left (add_nonneg (hQ.tap m hm) (mul_nonneg zero_le_two (zero_le_one.trans (H.levels.params (m+1)).columns_ge))) (orbitCost_one_le ..))
     let r:= φ (m+1); have hr: 0≤ r:= rem_nonneg ((hh.ticks _ hx hm').2)
     let x:=(Z (m+1)).x;have hv : weighted H F (ψ m) (m+1) x r ≤ d'*(r+F.coeffSize x):=by
       unfold Relay.weighted; rw [mul_add d']; have he : orbitCost F*F.coeffSize x*(ψ m+2*Γ (m+1))=d'*F.coeffSize x:=by unfold d'; ring
       rw [he,add_comm]; exact add_le_add (mul_le_mul_of_nonneg_right hd hr) le_rfl
     let u':= w m; let t':= w (m+1); let y:=‖alto H m d‖; let y':=‖alto H (m+1) d‖; have hu':0 ≤ u':= (hw _ hm hm'.le).le; have ht':0 ≤ t':= (hw _ hx hm').le
     have hJ:2*t'*(y'*weighted H F (ψ m) (m+1) x r)≤1:=by
       apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (norm_nonneg _)) (mul_nonneg zero_le_two ht'))
       exact le_trans (le_of_eq (b:=2*d'*(t'* y'*(r+F.coeffSize x))) (by ring)) ((mul_le_mul_of_nonneg_left (hh.rates _ hx hm') (show 0 ≤ 2*d' from by linarith only [hd])).trans (le_trans (le_of_eq (by unfold d';ring):_ ≤ 2*orbitCost F*(ψ m+2*Γ (m+1))*ζ (m+1)) (hQ.room m hm)))
     have hI : t'*(y*φ m)≤1:=by
       have hs:0 ≤ φ m:= rem_nonneg ((hh.ticks m hm hm'.le).2); have hζ': u'*y*φ m ≤ ζ m:= le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Work.G08.size_nonneg F (Z m).x)) (mul_nonneg hu' (norm_nonneg _))) (hh.rates m hm hm'.le)
       exact le_trans (mul_le_mul_of_nonneg_right (hp m hm hm') (mul_nonneg (norm_nonneg _) hs)) ((le_trans (le_of_eq (Eq.symm (mul_assoc ..))) hζ').trans ((le_mul_of_one_le_right ((mul_nonneg (mul_nonneg hu' (norm_nonneg _)) hs).trans hζ') (H.levels.params _).columns_ge).trans (hQ.coin m hm)))
     refine ⟨_,alto H (m+1) d* scalar a (x 0),_,_, hS.image (Wing.labelRoute z), hJ,hI,?_⟩
     simp only [← hG m hm hm'.le, ← hG (m+1) hx hm']; exact hL'
   intro m hm ht; have hy:= hh.ticks (m+1) (hm.trans m.le_succ) ht; let E:= (Z (m+1)); obtain ⟨ha,hP⟩:=hy
   have hK : Integrable (E.density 0 T (R (m+1))) (prior G _):=play_integrable H N h ht ha hP
   simp_rw [liftF,hx' m hm ht.le,hx' (m+1) (hm.trans m.le_succ) ht, hO m hm ht]; exact starship H a (o m) _ _ d (hh.votes m hm ht|>.1) hK _ (alto_at H m d)
end YM.MergeProof
