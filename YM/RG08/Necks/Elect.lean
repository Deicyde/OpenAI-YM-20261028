import YM.RG08.Necks.Lob
/-! # T ballots & rank, at SLOT ranges ≥ n transfer target.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Clef
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries
variable {G:Gauge}{n m d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "A₀"=>Loc G 1
local notation "E"=> Ed G Cover
variable (X:Labels.Frame G d)

-- budget for full outputs at rank≤E, all strict relative to given costing n. paired.
lemma older (D d e l n N:ℕ)(_hle:n≤N)(σ η:ℝ)(hs:0<σ)(hk:0<η)(hx:η≤1): ∃ J:ℝ→ℝ,Week (olderR N e l) J∧∀ W≥1,1≤J W∧∀{G:Gauge}{P:Patch}{K:KernelChoices}{Q R:Crew G P K}{δ:ℝ},Warmth η δ W e N d Q R→ η*Carrier.unitStep P.L≤σ→ ∀{S S':GrainS (Ed G Cover)}{B:ℝ},Folk D l S→Folk D l S'→0≤B→(∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) D hs B δ (S i r) (S' i r))→∀ i m,m≤N→(i<e∨i=e∧n < m)→
 Dyad (stance _) D hk (J W*B) δ (Q.land d l S i m) (R.land d l S' i m):=by
 let J(x:Fin (N+1)×Fin (e+1)):= portW x.1.val x.2.val l
 have hJ(i: Fin (N+1)×Fin (e+1)) : Wage (J i):=portHW i.1.val i.2.val l -- can't infer I
 let Y(w:ℝ):=1+∑ i,2*J i w
 let m:=olderR N e l
 have h₀(i):Week m (J i):=(grade_week (hJ i)).rise (Finset.le_sup (f:=fun s:Fin (N+1)×Fin (e+1)=> portR s.1.val s.2.val l) (Finset.mem_univ i))
 have hY:Week m Y:=by
   have h:Week (max 0 (0+m)) Y:= (Week.fixed _ zero_le_one).add (Week.sum univ _ (fun i _=> (Week.fixed _ (by positivity)).mul (h₀ i)))
   simpa only [zero_add,Nat.max_eq_right (Nat.zero_le _)] using h
 refine ⟨Y,hY,fun W hW=>?_⟩
 have ht(i):= (hJ i).nn hW
 refine ⟨le_add_of_nonneg_right (sum_nonneg fun i _=>by have hv:=ht i;positivity),?_⟩
 intro G P K Q R δ hw hσ S S' B hF hF' hB hv i m hm he
 let z:Fin (N+1)×Fin (e+1):=(⟨m,by omega⟩,⟨i,by omega⟩)
 have h1(j k)(hy:k≤l+j)(h:j < i∨j=i∧m<k):=hv j k hy (by omega)
 by_cases hN:m≤l+i
 · obtain ⟨h,h',hh,HH,-⟩:= (portFee z.1.val z.2.val l).choose_spec.2 (hw.prices (by omega:i≤e) hm) hk hx hσ hB hB hF hF' h1 (hv i m hN he)
   rw [hh,HH];apply (h.add h').mono
   have h3:2*J z W≤ Y W:=by unfold Y; apply le_trans _ (le_add_of_nonneg_left zero_le_one);exact single_le_sum (s:=univ) (f:=fun z=>2*J z W) (by intro i _;have hv:=ht i; positivity) (mem_univ z)
   change J z W*B+J z W*B≤ Y W*B;nlinarith only [h3,hB]
 rw [show Q.land d l S i m=0 from Classical.not_not.mp fun h=>hN ((Crew.living (d:=d) Q D S hF).inlet.lit i m h),show R.land d l S' i m=0 from Classical.not_not.mp fun h=>hN ((Crew.living (d:=d) R D S' hF').inlet.lit i m h)]
 apply (Dyad.zero hw.tooth.gift).mono;exact mul_nonneg (add_nonneg zero_le_one (sum_nonneg fun s _=>mul_nonneg (by norm_num) (ht s))) hB

lemma booth_spend (D d:ℕ)(X:Labels.Frame G d)(η:ℝ)(he:0<η):∃ H:ℝ,0≤H∧∀(e:ℕ){S S':GrainS (Ed G Cover)}(i:Accent X)(B δ:ℝ),Folk D l S→Folk D l S'→ 0≤B→0≤δ→ (∀ a k,a<e→k≤d→ Dyad (stance _) D he B δ (S a k) (S' a k)) →
 let k:=octave i; let F(M:GrainS (Ed G Cover)):= Trill.project X M e i-Trill.pix X i.ear i.test.play (M e k)
 ; |F S|≤H*B ∧ |F S'|≤H*B ∧ |F S-F S'|≤H*B*δ:=by
 obtain ⟨C,hC,H⟩:=pitch X D η he
 refine ⟨d*C,by positivity,?_⟩;intro e S S' i B δ hs hs' hB hδ h k F
 let u(T:GrainS E)(j:ℕ):=if k-j≤e then Trill.pix X i.ear i.test.play (T (e-(k-j)) j) else 0
 have hU(T:GrainS E): F T=∑ j∈range k,u T j:=by unfold F;rw [project_split];exact add_sub_cancel_right ..
 have hv(P:GrainS E)(b:ℝ)(hb:0≤b)(hP:Folk D l P)(hx:∀ a<e,∀ k≤d,Sings (stance _) D he (P a k) b): |F P|≤ (d:ℝ)*C*b:=by
    rw [hU];apply (abs_sum_le_sum_abs _ _).trans
    refine (sum_le_sum (g:=fun _=>C*b) (fun j hj=>?_)).trans ?_
    · have hR : j<k:=mem_range.mp hj;have hi:k≤d:= octave_le i; unfold u; split_ifs; apply H i j (by omega) (P (e-(k-j)) j) (permit_ready hP.inlet).coherent b hb (hx _ (by omega) _ (by omega)); rw [abs_zero];positivity
    rw [sum_const,card_range,nsmul_eq_mul,←mul_assoc];gcongr;exact octave_le i
 refine ⟨hv S B hB hs (fun a ha k hk=>(h a k ha hk).near),hv S' B hB hs' (fun a ha k hk=>(h a k ha hk).far),?_⟩
 rw [show F S-F S'=F (S-S') from ?_,mul_assoc (d*C:ℝ)]
 · exact hv _ _ (by positivity) (hs.sub hs') (fun a ha k hk=> (h a k ha hk).switch)
 unfold F; rw [Necks.ballot_minus X hs hs',show Trill.pix X i.ear _ ((S-S') e _)=_ from pix_minus X (permit_ready hs.inlet) (permit_ready hs'.inlet) _ _];ring

lemma ballot_chart (a:Accent X)(S:GrainS E):project X S 0 a=pix X a.ear a.test.play (S 0 (octave a)):=by
 rw [project_split];dsimp only; unfold Atrium.octave;rw [sum_eq_zero,zero_add] -- rfl maybe goals count
 intro i hi;rw [if_neg];simp only [mem_range] at hi;omega
end YM.RG08.Necks
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Clef
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries
variable {G:Gauge}{n m d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "A₀"=>Loc G 1
local notation "E"=> Ed G Cover
variable (X:Labels.Frame G d)
structure Docket (X:Labels.Frame G d){P:Patch}{K:KernelChoices}(Q R:Crew G P K)(D e l n:ℕ)(A J σ χ B c T ξ δ:ℝ)(hs:0<σ)(w:ℕ)(S S':GrainS E) :Prop where
 fare: let g:ℝ:=P.L.val;let a:=A*T/g+J*(B+χ);let a':=A*c/g+J*(B+χ)
       ; Tide X D w n A g σ a χ (J*B) hs (S e n) (Q.land d l S e n)∧ Tide X D w n A g σ a' χ (J*B) hs (S' e n) (R.land d l S' e n) -- second requires weakening B threshold exact if old J=0; OK
 rated:let g:ℝ:=P.L.val;let b:=J*(B+c)*δ
       ; Ripple X D n σ (A*ξ/g+b) b hs (Q.land d l S e n) (R.land d l S' e n)
 booth:let g:ℝ:=P.L.val
       ;∀ i:Accent X, n≤octave i→ let _k:=gamut i;let r:=project X (Q.land d l S) e i;let r':=project X (R.land d l S') e i
                                  ; |r| ≤ A*χ*g^(d-w)+J*B ∧ |r'|≤ A*χ*g^(d-w)+J*B ∧ |r-r'|≤ J*(B+c)*δ ∧ (e=0→B=0→ octave i=n→ gamut i≤w→ r = g^(d-gamut i)*project X S 0 i ∧ r'=g^(d-gamut i)*project X S' 0 i)

lemma DocketBill (D l e n j t W0:ℕ)(H:Hol G)(K:KernelChoices)(σ η τ μ V:ℝ)(hv:Novice σ τ η μ V d D l e n j t)(hN:n≤W0)(hD:d ≤ W0) :∃ A:ℝ,∃ J:ℝ→ℝ,1≤A∧Week (docketR n e l d W0) J∧∀ W≥1,1≤J W∧∀ {P:Patch}{Q R:Crew G P K}{S S':GrainS (Ed G Cover)}{δ:ℝ}, Race σ τ η μ V W δ D d e W0 j t Q R→
 Folk D l S → Folk D l S'→∀ B T T0 c κ χ:ℝ,0≤B→0≤T→0≤T0→0≤c→0≤κ→0≤χ→(∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) D hv.paid B δ (S i r) (S' i r))→
 (∀ i≤l+e,Sings (stance _) D hv.paid (S e i) T∧Sings (stance _) D hv.paid (S' e i) T)→ Dyad (stance _) D hv.paid T δ (S e n) (S' e n)→
 Sings (stance _) D hv.paid (S e n) T0→Sings (stance _) D hv.paid (S' e n) c→Sings (stance _) D hv.paid (S e n-S' e n) κ→(∀ i:Accent X,octave i=n→|project X S e i|≤χ∧project X S e i=project X S' e i)→
 ∀ w≤d,(w=0 ∨ B=0∧∀ i:Accent X,octave i=n→ gamut i<w→ project X S e i=0)→ Docket X Q R D e l n A (J W) η χ B c T0 κ δ hv.out' w S S':=by
 obtain ⟨A,F,hA,hF,F'⟩:= conquer X H l D e n j t σ τ η μ V hv K
 obtain ⟨J,hJ,HJ⟩:= older D d e l n W0 hN σ η hv.paid hv.out' hv.warm
 obtain ⟨p,hp,hpix⟩:= pitch X D η hv.out'
 obtain ⟨C,hC,hB⟩:=booth_spend (l:=l) D d X η hv.out'
 let L(x:ℝ):= F x+ J x*(p+C)
 refine ⟨A,L,hA,hF.add (hJ.mul (Week.fixed _ (by positivity))),fun W hW=>?_⟩
 have hj:= (HJ W hW).1;have hf:= (F' W hW).1
 have hJ: F W ≤ L W:= by unfold L; have hx:= (show 0 ≤ J W by linarith); nlinarith only [hp,hC,hx] -- on ≤ ??
 have hL:1≤L W:=hf.trans hJ
 refine ⟨hL,?_⟩;intro P Q R S S' δ hr hs hs' B T T0 c κ χ hb _ h0 hc hκ hχ ht hS hY hr0 hC' hk Hs w hD' H_
 let M:=Q.land d l S;let N:=R.land d l S';let g:ℝ:=P.L.val
 obtain ⟨hu,hx,hh⟩:= (F' W hW).2 (Q:=Q) (R:=R) (δ:=δ) (show Race _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ from ⟨hr.aps.prices le_rfl hN,hr.sold,hr.sold'⟩) hs hs' B T T0 c κ χ ht hS hY hr0 hC' hk hb h0 hc hκ hχ Hs w hD' H_
 have he(i m:ℕ)(hi:m≤W0)(hm:i<e∨i=e∧n < m): Dyad (stance _) D hv.out' (J W*B) δ (M i m) (N i m):=(HJ W hW).2 hr.aps (hr.sold.nim.trans (half_le_self hv.paid.le)) hs hs' hb ht i m hi hm
 have hδ:=hr.aps.tooth.gift
 have hU:=Crew.living (d:=d) Q D S hs; have hV:=Crew.living (d:=d) R D S' hs'
 have hv':0≤F W:=zero_le_one.trans hf;have hj':0≤J W:=zero_le_one.trans hj
 have hz: F W*(B+c)*δ ≤ L W*(B+c)*δ:=by gcongr
 have ha: F W*(B+χ)≤L W*(B+χ):=by gcongr
 have hb':F W*B≤L W*B:=by gcongr
 constructor
 · constructor
   · exact ⟨hu.ready',hu.cost0.mono le_rfl le_rfl (fun _=>le_rfl) (by gcongr),fun i hi=>(hu.pose i hi).trans (by gcongr),fun i hi hh ht=>hu.landed i hi hh (le_antisymm (hb'.trans (le_of_eq ht)) (mul_nonneg hv' hb))⟩
   exact ⟨hx.ready',hx.cost0.mono le_rfl le_rfl (fun _=>le_rfl) (by gcongr),fun i hi=>(hx.pose i hi).trans (by gcongr),fun i hi hh ht=>hx.landed i hi hh (le_antisymm (hb'.trans (le_of_eq ht)) (mul_nonneg hv' hb))⟩
 · refine ⟨hh.spent.mono le_rfl le_rfl (fun _=>le_rfl) (by gcongr),fun i hi=>(hh.posed i hi).trans hz⟩
 dsimp only; intro i hi;let r:=octave i;have hr': r≤d:=octave_le i
 let s:=fun S:GrainS E=>pix X i.ear i.test.play (S e r)
 let a(M:GrainS E):=project X M e i
 change |a M|≤_ ∧|a N|≤_ ∧ |a M-a N|≤ _ ∧ _
 obtain ⟨h₁,h₂,h₃⟩:=hB e (S:=M) (S':=N) i (J W*B) δ hU hV (by positivity) hδ (fun a k ha hf=>he _ _ (hf.trans hD) (.inl ha))
 let t:= A*χ*g^(d-w); have ht0:0 ≤ t:=by unfold t g;have ha':0 ≤ A:=zero_le_one.trans hA;positivity
 have hp': |s M| ≤ t+ F W*B+p*(J W*B)∧ |s N| ≤ t+F W*B+p*(J W*B) ∧ |s M-s N| ≤ F W*(B+c)*δ+p*((J W*B)*δ):=by
    have hp0:0≤p*(J W*B):=by positivity
    rcases eq_or_lt_of_le hi with hc'|hR
    · refine ⟨le_trans (show |s M|≤t+F W*B from by unfold s r; rw [← hc'];exact hu.pose i hc'.symm) (le_add_of_nonneg_right hp0),le_trans (show |s N|≤t+F W*B from by unfold s r; rw [←hc'];exact hx.pose i hc'.symm) (le_add_of_nonneg_right hp0),?_ ⟩
      exact le_trans (show |s M-s N| ≤ F W * (B+c)*δ from by unfold s r; rw [←hc']; exact hh.posed i hc'.symm) (le_add_of_nonneg_right (by positivity))
    have hh:=he e r (hr'.trans hD) (.inr ⟨rfl,hR⟩)
    have he''(Z:GrainS E){a:ℝ}(h1:Ready D G r (Z e r))(h2:0 ≤ a)(h3:Sings (stance _) D hv.out' (Z e r) a): |s Z| ≤ p*a:=hpix i r hr' _ h1.coherent _ h2 h3
    have hR{V:GrainS E}(hvX:Ready D G r (V e r))(hh:Sings (stance _) D (show 0<η from hv.out') (V e r) (J W*B)):|s V|≤t+F W*B+p*(J W*B):=(he'' V hvX (by positivity) hh).trans (le_add_of_nonneg_left (by positivity))
    refine ⟨hR (permit_ready hU.inlet) hh.near,hR (permit_ready hV.inlet) hh.far,?_⟩
    have H':s M-s N=s (M-N):=(pix_minus X (permit_ready hU.inlet) (permit_ready hV.inlet) i.ear i.test.play).symm
    rw [H'];exact (he'' _ (Trill.permit_ready (hU.sub hV).inlet) (by positivity) hh.switch).trans (le_add_of_nonneg_left (by positivity))
 let b(z:GrainS E):=a z-s z
 have H'(z):a z=s z+b z:=by unfold b;ring
 have h1:|a M| ≤ t+L W*B:= calc
     _ ≤ |s M|+|b M|:=by nth_rw 1 [H' M];apply abs_add_le
     _ ≤ t+F W*B+p*(J W*B)+C*(J W*B):=add_le_add hp'.1 h₁
     _ =_:=by unfold L;ring
 have h2:|a N| ≤ t+L W*B:= calc
     _ ≤ |s N|+|b N|:=by nth_rw 1 [H' N];apply abs_add_le
     _ ≤ t+F W*B+p*(J W*B)+C*(J W*B):=add_le_add hp'.2.1 h₂
     _ =_:=by unfold L;ring
 refine ⟨h1,h2,?_,?_⟩
 · apply (le_trans (b:= |s M-s N|+|b M-b N|) _ ((add_le_add hp'.2.2 h₃).trans ?_));swap
   · unfold L;nlinarith only [show 0≤J W*(p+C)*c*δ by positivity]
   nth_rw 1 [H' M,H' N];rw [add_sub_add_comm];exact abs_add_le ..
 intro hz hB hN hG;have hu':F W*B=0:=by rw [hB,mul_zero]
 subst e
 rw [ballot_chart,ballot_chart,ballot_chart,ballot_chart,hN];exact ⟨hu.landed i hN hG hu',hx.landed i hN hG hu'⟩
end YM.RG08.Necks
