import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Glowing
import YM.MergeProof.Largo
import YM.MergeProof.Ruby
import YM.MergeProof.TeamPygmy
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Sieve
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Melange
import YM.Planned.STATIONARY_JET_PORT.Tariff
import YM.UVNext.COUPLING_RESET.Tuning
/-! Sings the actual aligned calibrated terminal over one anchor and ANY material point. -/
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
def soarF (m:ℕ):Config G (H.S.side m p)→ℂ:= radiant (alto H m d) a (o m) (((Gx m).plays V).exponentialEntry 0 T (R m))
def soarK (m:ℕ): Box (H.S.side m p)→ Config G (H.S.side m p)→ℂ:= sunny (R m) ((Gx m).plays V).forced a (o m) (alto H m d)
local notation "g!"=> soarK H N p M V a o
local notation "f!"=> soarF H T N p M V a o
local notation "T!"=> stepUp a (o N) (initial T H N p V 0)
local notation "χ"=> (fun i=>coin (R i) (f i) (g i))
local notation "Y!"=> (fun i=>profile (R i).activities (g i))
structure Wild :Prop where
    stocked m : k ≤ m → m≤N→ Dominated (g m)
    writes U : ((R N).eval U:ℂ)*b U= χ N U
    patent : ∃ (z : MergeProof.Response G (H.S.side N p)) (r:ℝ), Attainment (R N).p (o N) z r ∧ w N*r ≤ u N ∧ hook (R N).activities (R N).p.threshold z=Y! N
    sways m : k ≤ m →∀ hN:m<N,∃ (ψ:Set PhysicalNext.Repeat.Lotus.Wing) (v:ℂ)(s t:ℝ), ψ.Finite∧ 2*w (m+1)*s ≤ 1 ∧ w (m+1)*t ≤ 1 ∧ Tale ψ (o (m+1)) (o m) 1 (f (m+1)) (Y! (m+1)) (Y! m) v s t (D N p m hN)
    feeds m : k ≤ m → m<N → χ m= (H.levels.clock.op m p).push ((R (m+1)).beta) (χ (m+1))
lemma sweet (h:H.Selected)(he:T.Sound A)(hh:Sung T H N p A W k M)
    (hw:∀ m:ℕ,k ≤ m → m≤N → 0 < w m)(hp:∀ m:ℕ,k ≤ m→m<N→w (m+1) ≤ w m) (hC:∀ m:ℕ,k ≤ m→m≤N→w m*bond H N p M m V ≤ ζ m)
    (hQ:Fiesta H F ζ ψ k)(hx:Banks H F t u ζ N) (hf: coverNumber (P N).B (T.footprint (0:Site (H.S.side N p))) ≤ 1)(hV:∀ (i:F.Index)(U:Config G (H.S.side N p)), ‖T.places (Size.axis F i) 0 U‖ ≤ t)
    (hO:∀ m:ℕ,k ≤ m→m<N→ o (m+1)=(H.levels.clock.op m p).ratio.embed (o m))
    (hZ:profile (R N).activities ((Gx N).plays V).forced=hook (R N).activities (R N).p.threshold (booster T (R N) 0 V))
    (hD:∀ m:ℕ,k ≤ m →∀ hm:m<N, Carol T H N p m (D N p m hm) (Gx (m+1)) (Gx m) (ψ m) ∧ SoundDoor (H.levels.clock.op m p) (D N p m hm)) : ∃ g:∀ m:ℕ,ℕ → Config G (H.S.side m p)→ℂ,
        Wild H u k N p o w (f!) g (T!) D ∧ ∀ m:ℕ,k ≤ m→m≤N→profile (R m).activities (g m)= g! m:=by
   choose! g hG hd hx' using fun m:ℕ=> fun hK:k ≤ m=> fun hn:m≤N=> sparkling H A T ((Gx m).plays V) a (o m) (X m d) h 0 hn he (hh.earned m hK hn |>.earns V |>.1) (hh.earned m hK hn|>.earns V|>.2)
   have hk:= hh.ahead
   refine ⟨g,⟨hd,fun U=>?_,?_,?_,?_⟩,fun m he hx=>(hG m he hx).symm⟩
   · exact (mural H A T N p M V a (o N) hh.head h U).trans ((congr_fun (hx' N hk le_rfl) _).symm)
   · obtain ⟨π⟩:= (h.represents N p N le_rfl).good.labels.moves a.1 (o N); let Z:= booster T (R N) 0 V
     obtain ⟨r,hP,H'⟩:= erected H A T W ζ u t k N p M V (w N) (hT:=he) hV h hh (hC N hk le_rfl) hx hf (hw N hk le_rfl|>.le)
     have hw:= rise a (o N) hP; rw [show affine a.1 (o N) 0=o N by simp [affine]] at hw
     have hy:= stack_of hw (X N d); refine ⟨(X N d) • upwards a (o N) Z,_,hy,H',?_⟩
     rw [hook_scale]; unfold Z; rw [hooked a (o N) π, ← hZ]; exact hG N hk le_rfl
   · intro m hm hm'; let S:= H.levels.clock.op m p; let c:= S.ratio.embed (o m); obtain ⟨⟨s,hS,hL⟩,hK⟩:= hD m hm hm'; let v:ℂ:=((H.S.block m).val:ℂ)^d
     have hy:= hh.earned m hm hm'.le; let τ:= ((H.levels.clock.op m p).ratio.embed (o m)); obtain ⟨z⟩:= (h.represents N p (m+1) hm').good.labels.moves a.1 (S.ratio.embed (o m)); have hF:= hO m hm hm'
     have hL':= (hL V).gain hK a (o m) z (show scalar a v=v from by unfold scalar v; split <;> simp) |>.pitch (X (m+1) d) (X m d) (alto_at H m d)
     simp only [← hF, show affine a.1 (o m) 0=o m by simp [affine], show affine a.1 (o (m+1)) 0=o (m+1) by simp [affine]] at hL'
     have hx : k ≤ m+1:= hm.trans m.le_succ; obtain ⟨hI,hJ⟩:= cost_step H A T ζ ψ k N p M m V _ _ (hC _ hm hm'.le) (hw _ hm hm'.le|>.le) (hw _ hx hm'|>.le) hQ (hp m hm hm') hm (hC _ hx hm') hy
     refine ⟨_,alto H (m+1) d* scalar a ((Gx (m+1)).index V 0),_,_, hS.image (Wing.labelRoute z), hJ,hI,?_⟩
     simp only [← hG m hm hm'.le, ← hG (m+1) hx hm']; exact hL'
   intro m hm ht; have hy:= hh.earned (m+1) (hm.trans m.le_succ) ht; let E:= (Gx (m+1)).plays V; obtain ⟨ha,hP⟩:=hy.earns V
   have hK : Integrable (E.density 0 T (R (m+1))) (prior G _):=play_integrable H N h ht ha hP
   simp_rw [soarF,hx' m hm ht.le,hx' (m+1) (hm.trans m.le_succ) ht, hO m hm ht]; exact starship H a (o m) _ _ d ((hh.step m hm ht).values V) hK _ (alto_at H m d)
end YM.MergeProof
