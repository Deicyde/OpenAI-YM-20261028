import YM.MergeProof.Bakery
import YM.MergeProof.Brioche


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
variable (Q:∀ i:ℕ,Solo F H p i){l:ℕ} (s j:ℕ)(h:l ≤ k)
   {Z:Coefficient F (H.S.side N p)} {U E e B:ℝ} {L:MergeProof.Response G (H.S.side N p)}
set_option quotPrecheck false
local notation "Y"=> (dualize H N p M l N Q (-(Q l).a))
-- Carried resume exists also for non-top origins; Yeast here from actual Wilson top.
lemma toast (hT:H.Selected)(hA:T.Sound A) (hk:l ≤ k)(hh:Sung T H N p A W l M)(hw:k≤N)
    (hC:Challenge T H N p A W M l N Q)(ht:∀ i:ℕ,k ≤ i →∀ hm:i<N, Accord T H N p M (ψ i) i (D N p i hm) (Q (i+1)) (Q i))
    (hp:Q N= Relay.pair H N p M Z t) (he:∀ i:ℕ,k ≤ i → i≤N → gainChart H N i*((Y).cost i + F.coeffSize ((Y).voice i).x) ≤ E)
    (hK: Z.Format 0 A (R N))(hr: Z.remBound 0 (R N) (Real.sqrt (H.levels.clock.forcedAllowance N)) t)
    (hq: t+F.coeffSize Z.x ≤ E)(hb: Attainment (R N).p 0 L B)
    (hL: profile (R N).activities Z.forced=hook (R N).activities (R N).p.threshold L)(hu:∀ x,profile (R N).activities ((Gx N).plays x).forced=hook (R N).activities (R N).p.threshold (booster T (R N) 0 x))
    (hy:B*ζ N ≤ u N*E)(ho : ∀ V, Z.density 0 T (R N) V=((H.S.a N:ℂ)^d)*((R N).eval V:ℂ)* b V)
    (hf:∀ i,k ≤ i→ i≤N → 0 < w i) (hz:∀ i,k ≤ i→i≤N→0≤ζ i) (hX:∀ i,k ≤ i→i≤N→ w i*‖X i d‖*(E/gainChart H N i) ≤ ζ i/4)
    (hθ:0 < E)
    (hv:Banks H F e u ζ N) (hx: coverNumber (P N).B (T.footprint (0:Site (H.S.side N p))) ≤ 1)(hV:∀ (i:F.Index)(U:Config G (H.S.side N p)), ‖T.places (Size.axis F i) 0 U‖ ≤ e) :
    Yeast H A T ζ u ψ k N p w (b + initial T H N p (-(Q l).a) 0) D (Y).voice (Y).cost:=by
    let f:= -(Q l).a
    have hg (i) (hi:k ≤ i) (hp:i≤N):= keys T H N p A M f (hC.chairs i (hk.trans hi) hp) (hh.earned i (hk.trans hi) hp)
    have hE (i) (hi:k ≤ i) (hw:i≤N) : (Y).cost i+F.coeffSize ((Y).voice i).x ≤ E/gainChart H N i:= (le_div_iff₀ (show 0<gainChart H N i from Real.exp_pos _)).mpr ((mul_comm ..).trans_le (he i hi hw))
    let y:= Q N; let x:=(Y).voice N; let J:= Gx N; let S:= R N
    have hW:=originate T H N p A M le_rfl hT (hh.earned N (hk.trans hw) le_rfl) hK hr (show F.coeffSize Z.x+t ≤ E from (add_comm ..).trans_le hq)|>.2 f; rw [← hp] at hW
    have hB:Sung T H N p A W l M:=hh
    have hs: x.density 0 T S = Z.density 0 T S + (J.plays f).density 0 T S:= hW.2.1
    refine ⟨fun i hi hw=> (hg _ hi hw).2,fun i hi hw=>?_,fun i hi hw=> ⟨(hC.ships i (hk.trans hi) hw).debt f,?_⟩,?_,fun U=>?_⟩
    · exact (mul_le_mul_of_nonneg_left (hE _ hi hw) (mul_nonneg (hf _ hi hw|>.le) (norm_nonneg _))).trans ((hX _ hi hw).trans (div_le_self (hz _ hi hw) (by norm_num)))
    · obtain ⟨p,hP,hV⟩:= (ht i hi hw).plays; exact ⟨p,hP,hV f⟩
    · let c:= J.index f
      have hξ := hg N hw le_rfl; have hn:= hh.earned N (hk.trans hw) le_rfl; have hx' : x.x= Z.x+c:= hW.1; have hf':F.coeffSize c ≤ 2*E:=by
         have hv : c=x.x-Z.x:=by rw [hx']; abel
         have hs' := hE N hw le_rfl; rw [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at hs'
         have he : F.coeffSize x.x ≤ E:= le_trans (b:=(Y).cost N+F.coeffSize x.x) (le_add_of_nonneg_left (rem_nonneg hξ.2.2)) hs'
         have hp: F.coeffSize (-(Z.x))=F.coeffSize Z.x:=by simp [Labels.Frame.coeffSize]
         rw [hv,sub_eq_add_neg]; apply (Size.add F _ _).trans; rw [hp]; linarith only [hq,rem_nonneg hr,he]
      let i:=w N; let j:=‖alto H N d‖; have h':i*j*E≤ζ N/4:=by simpa only [gainChart,sub_self,mul_zero,Real.exp_zero,div_one] using hX N hw le_rfl
      have hi:0 < i:= hf N hw le_rfl
      have hp': (2*i)*bond H N p M N f ≤ ζ N:=by
         change (2*i)*(j*F.coeffSize c) ≤ _; have hv:= mul_le_mul_of_nonneg_left hf' (mul_nonneg (norm_nonneg (X N d)) (show 0 ≤ 2*i by linarith only [hi])); linarith only [hv,h']
      obtain ⟨a,hP,H'⟩:= erected H A T W ζ u e l N p M f (2*i) (hT:=hA) hV hT hh hp' hv hx (show 0≤ 2*i by linarith only [hi]); have hB':0≤ B:=sumBudget_credit hb.toll.choose_spec.1
      have ha' : i*j*B ≤ u N/2:=by
         apply le_of_mul_le_mul_right (a:=E) _ hθ
         have hx := mul_le_mul_of_nonneg_right h' hB'; have hζ:= hz N hw le_rfl; have hT : 0≤ u N*E:= (mul_nonneg hB' hζ).trans hy; linarith only [hy,hT,hx]
      refine ⟨L+booster T (R N) 0 f,B+a, hb.plus hP,?_,?_⟩
      · change i*(j*(B+a)) ≤ _; linarith only [ha',H']
      let V:= (Gx N); have hI := inkL V.plays V.charge hn.book (fun i=> (hn.earns i).2); let q:=Q N; let Q':= Relay.pair H N p M Z t; have hΩ:q=Q':=hp
      rw [hook_add,← hL,← hu]; change profile S.activities (q.bar M f).forced=_+_
      rw [hΩ]; let c':= Q'.a
      have hp : Q'.sil.remBound 0 (R N) (Real.sqrt (H.levels.clock.forcedAllowance N)) (t+V.charge (-c')):= (presentation hK hr (hn.earns (-c')).1 (hn.earns (-c')).2).2
      change profile S.activities (beside ..).forced=_+_; rw [duo_profile hp (hn.earns (c'+f)).2,show profile (R N).activities Q'.sil.forced= _ from duo_profile hr (hn.earns (-c')).2]; let F'(x):=profile S.activities ((M.tone N).plays x).forced; have hu:IsLinearMap ℂ F':=hI; change _+ F' (-c')+F' (c'+f)=_+F' f
      rw [hu.map_add,show F' (-c')= -F' c' from (IsLinearMap.mk' F' hu).map_neg c']; abel
    change x.density 0 T S U=_; rw [hs]; simp only [Pi.add_apply,mul_add]; rw [show (J.plays f).density 0 T S U= _ from hh.head.earns f U,show Z.density 0 T S U = _ from ho U]
end YM.MergeProof
