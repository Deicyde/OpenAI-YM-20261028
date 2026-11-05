import YM.RG08.Necks.Tides
/-! # Full marked step solved before matrix. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Necks
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Clef
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries
variable {G:Gauge}{n m d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
local notation "A₀"=>Loc G 1
local notation "E"=> Ed G Cover
structure Race (σ τ η μ V W δ:ℝ)(D d k n j t:ℕ){K:KernelChoices}(Q R:Crew G P K):Prop where
 aps:Warmth η δ W k n d Q R
 sold:Stream σ τ η μ V W d j t Q
 sold':Stream σ τ η μ V W d j t R

variable (X:Labels.Frame G d)
-- Bottles are at D test assessment. χ=1,w column weight concentrated when e=0,n=l, B earlier =0. for e>0 χ=0 if calibrated/plaque, else paid. Δχ
-- P solver typically W.N and χcost separately; T unrestricted and same-level T influences through changes of geometry only. β for booth trajectory; paired δ>0 by choosing brutal rate even for unchanged. T for SELF INPUT VARIATION **no absolute** law preserved.
structure Tide (X:Labels.Frame G d)(D w n:ℕ)(ρ g σ W χ B:ℝ)(h:0<σ)(M F:Pack n (Ed G Cover)):Prop where
 ready':Ready D G n F
 cost0:Sings (stance _) D h F W
 pose :∀ i:Accent X,octave i=n→ |pix X i.ear i.test.play F|≤ ρ*χ*g^(d-w)+B
 landed :∀ i:Accent X,octave i=n→ gamut i≤w→ B=0→pix X i.ear i.test.play F=g^(d-gamut i)*pix X i.ear i.test.play M
-- paired Slope journey
structure Ripple (X:Labels.Frame G d)(D n:ℕ)(σ W B:ℝ)(h:0<σ)(F F':Pack n (Ed G Cover)):Prop where
 spent:Sings (stance _) D h (F-F') W
 posed:∀ i:Accent X,octave i=n→ |pix X i.ear i.test.play F-pix X i.ear i.test.play F'|≤ B

-- constants depend only on pre before L. 
set_option maxHeartbeats 800000
lemma conquer (H:Hol G)(l D e n j t:ℕ)(σ τ η μ V:ℝ)(h:Novice σ τ η μ V d D l e n j t)(K:KernelChoices):∃ A:ℝ,∃ J:ℝ→ℝ,1≤A∧ Week (conquerR n e l d) J ∧ ∀ W≥1,1≤J W ∧ ∀ {P:Patch}{Q R:Crew G P K}{δ:ℝ},Race σ τ η μ V W δ D d e n j t Q R→∀{S S':GrainS (Ed G Cover)},Folk D l S→Folk D l S'→∀ (B T T' c ζ χ:ℝ),
 (∀ i r,r≤l+i→(i<e∨i=e∧n<r)→ Dyad (stance _) D h.paid B δ (S i r) (S' i r))→
 (∀ i≤l+e,Sings (stance _) D h.paid (S e i) T∧Sings (stance _) D h.paid (S' e i) T)→ Dyad (stance _) D h.paid T δ (S e n) (S' e n)→
 Sings (stance _) D h.paid (S e n) T'→Sings (stance _) D h.paid (S' e n) c→Sings (stance _) D h.paid (S e n-S' e n) ζ→0≤B→0≤T'→0≤c→0≤ζ→0≤χ→(∀ i:Accent X,octave i=n→ |project X S e i|≤χ∧ project X S e i=project X S' e i)→
 ∀ w≤d,(w=0 ∨ B=0∧∀ i:Accent X,octave i=n→ gamut i<w→project X S e i=0)→
 let g:ℝ:=P.L.val
 let β:=A*T'/g+J W*(B+χ); let β':= A*c/g+J W*(B+χ);let N:=Q.land d l S e n;let N':=R.land d l S' e n
 let C:=J W*(B+c)*δ
 ; Tide X D w n A g η β χ (J W*B) h.out' (S e n) N ∧Tide X D w n A g η β' χ (J W*B) h.out' (S' e n) N'∧ Ripple X D n η (A*ζ/g+C) C h.out' N N':=by
 obtain ⟨A,F,hA,hF,H'F,U⟩:=drive X H l D e n j t σ τ η μ V h K
 let u:=portW n e l;let z:=cometW n d
 have hu:Week (portR n e l) u:=grade_week (portHW n e l)
 have hz:Week (cometR n d) z:=grade_week (cometHW n d)
 obtain ⟨p,hp,hP⟩:=pitch X D η h.out'
 let J(w:ℝ):=(1+p)*(1+F w+u w+z w)
 have h0:Week (conquerR n e l d) J:=by
   have hy: Week (0+max (max (max 0 (driveR n)) (portR n e l)) (cometR n d)) J :=(Week.fixed _ (by positivity)).mul ((((Week.fixed 1 zero_le_one).add hF).add hu).add hz)
   simpa [conquerR] using hy
 refine ⟨A,J,hA,h0,fun W hW=>?_⟩
 have hu' := hu.nn hW;have hz':= hz.nn hW; have hF':=H'F W hW
 have hJ:1≤J W:=by unfold J;nlinarith only [hu',hz',hF',hp]
 refine ⟨hJ,?_⟩
 intro P Q R δ hr S S' hs hs' B T T' c ξ χ hv hf ht hL hr' hD hB hT' hc hξ hχ hU w hD' hw g β β' Y Y' C
 have hd:=hr.sold;have hd':=hr.sold';have hδ:=hr.aps.tooth.gift;have hT:=ht.price
 have h1:∀ i<e,∀ r≤l+i,Sings (stance _) D h.paid (S i r) B:=fun i hi r hk=>(hv i r hk (Or.inl hi)).near
 have h1':∀ i<e,∀ r≤l+i,Sings (stance _) D h.paid (S' i r) B:=fun i hi r hk=>(hv i r hk (Or.inl hi)).far
 have hη:η*Carrier.unitStep P.L≤σ:= hd.nim.trans (half_le_self (le_of_lt h.paid))
 obtain ⟨H₁,H₂,H₃,H₄,H₅,-⟩:= (portFee n e l).choose_spec.2 hr.aps h.out' h.warm hη hB hT hs hs' hv ht
 have HY:Ready D G n Y:= permit_ready (Q.living D S hs).inlet
 have HY':Ready D G n Y':= permit_ready (R.living D S' hs').inlet
 let a:=Q.cast d S e n;let a':=R.cast d S' e n;let t:=Q.cast d S' e n;let b:=Q.string d l S e n;let b':=R.string d l S' e n
 obtain ⟨ha,hR,hI⟩:=U hd hs w B T T' χ h1 (fun i hi=>(hf i hi).1) hL hχ hB hT hT' (fun i hi=>(hU i hi).1) hD' hw
 have hV(i:Accent X)(hi:octave i=n): |project X S' e i|≤χ:= (congrArg abs ((hU i hi).2).symm).trans_le ((hU i hi).1)
 obtain ⟨ha',hR',hI'⟩:=U hd' hs' w B T c χ h1' (fun i hi=>(hf i hi).2) hr' hχ hB hT hc hV hD' (hw.imp_right (fun h=> ⟨h.1,fun i hi hv=> (hU i hi).2.symm.trans (h.2 _ hi hv)⟩))
 let Z:=S-S'
 have hx:=hs.sub hs'
 obtain ⟨hx',hR'',hI''⟩:=U hd hx 0 (B*δ) (T+T) ξ 0 (fun i hi r hh=>(hv i r hh (Or.inl hi)).switch) (fun i hi=>( (hf i hi).1).sub ((hf i hi).2) hT hT) hD le_rfl (mul_nonneg hB hδ) (by positivity) hξ (fun i hi=>by rw [ballot_minus X hs hs' i,(hU i hi).2,sub_self,abs_zero]) (Nat.zero_le _) (Or.inl rfl)
 have hX:= (comet n d).choose_spec.2 hr.aps h.paid h.out' h.warm hη S' hc ((Trill.permit_ready (e:=e) (n:=n) hs'.inlet).coherent) hr'
 have hY:b=Y-a:=eq_sub_iff_add_eq'.mpr (Eq.symm H₃) -- addition a+b case
 have hY':b'=Y'-a':=eq_sub_iff_add_eq'.mpr (Eq.symm H₄)
 have hl :Ready D G n b:=hY ▸ Ready.minus HY hR
 have hl':Ready D G n b':=hY' ▸ Ready.minus HY' hR'
 have hr0:Ready D G n t:=by
    obtain ⟨H',H''⟩:=Trill.foreLyrics K Q.fine S' (permit_ready (e:=e) (n:=n) hs'.inlet) hd.place h.pre (zero_lt_one.trans_le hW) d
    exact ⟨H',H'',η,h.out',_,mul_nonneg hz' hc,hX.near⟩
 have hE:u W + F W≤J W:=by unfold J; nlinarith only [hp,hu',hz',hF']
 have hE': F W+p*u W ≤ J W:=by unfold J;nlinarith only [hp,hu',hz',hF']
 have hE'':F W+p*z W+p*u W≤J W:=by unfold J;nlinarith only [hp,hu',hz',hF']
 have hF0:0≤F W:=zero_le_one.trans hF'
 have hu0:F W≤J W:=le_trans (le_add_of_nonneg_left hu') hE
 have hz0: u W+z W≤J W:=by unfold J;nlinarith only [hp,hF',hu',hz']
 have ha0:0≤A:=zero_le_one.trans hA
 have hg:0 ≤ g:= Nat.cast_nonneg _;have hG:0 ≤ Carrier.unitStep P.L:=(Carrier.unitStep_pos _).le
 let μ(S:ℝ):=A*S*Carrier.unitStep P.L+F W*(B+χ)
 let γ(S:ℝ):=A*S/g+J W*(B+χ)
 have hq{S:ℝ}: μ S+u W*B ≤ γ S:=by unfold μ γ;rw [div_eq_mul_inv];change A*S*g⁻¹+ F W *(B+χ)+u W*B ≤ A*S*g⁻¹+ J W*_; nlinarith only [hE,hu0,hχ,hB]
 have hqa{X X' S:Pack n E}{T:ℝ}(hY:X=X'+S)(h₁:Sings (stance _) D h.out' X' (μ T))(h₂:Sings (stance _) D h.out' S (u W*B))(h0:0≤T): Sings (stance _) D h.out' X (γ T):=by
    rw [hY];exact (h₁.add h₂ (by unfold μ;positivity) (mul_nonneg hu' hB)).mono le_rfl le_rfl (fun _=>le_rfl) hq
 have hqb{F₀ X₁ L1 L2:Pack n E}(hY:F₀=L1+L2)(hV:Ready D G n L1)(hQ:Ready D G n L2)(hv:Sings (stance _) D h.out' L2 (u W*B))(i:Accent X)(hi:octave i=n)
  (H:|pix X i.ear i.test.play L1| ≤ A*χ*g^(d-w)+F W*B∧ (gamut i≤w → B=0→pix X i.ear i.test.play L1=g^(d-gamut i)*pix X i.ear i.test.play X₁)):
  |pix X i.ear i.test.play F₀| ≤ A*χ*g^(d-w)+J W*B ∧ (gamut i≤w→J W*B=0→pix X i.ear i.test.play F₀=g^(d-gamut i)*pix X i.ear i.test.play X₁):=by
   have hn:n≤d:=hi ▸ octave_le i
   have hz:=hP i n hn L2 hQ.coherent (u W*B) (mul_nonneg hu' hB) hv
   rw [hY,pix_plus X hV hQ];refine ⟨(abs_add_le ..).trans (le_trans (add_le_add H.1 hz) ?_),?_⟩
   · nlinarith only [mul_le_mul_of_nonneg_right hE' hB]
   intro hi hZ;have Hβ:B=0:= (mul_eq_zero.mp hZ).resolve_left (ne_of_gt (zero_lt_one.trans_le hJ))
   rw [H.2 hi Hβ,show pix X i.ear i.test.play L2=0 from abs_eq_zero.mp (le_antisymm (by simpa only [Hβ,mul_zero] using hz) (abs_nonneg _)),add_zero]
 have hYp : Y=a+b:=H₃;have hYq:Y'=a'+b':=H₄
 have hbc:Sings (stance _) D h.out' b (u W*B):=H₂.near
 have hbc':Sings (stance _) D h.out' b' (u W*B):=H₂.far
 refine ⟨⟨HY,hqa hYp ha hbc hT',fun i hi=> (hqb hYp hR hl hbc i hi (hI i hi)).1,fun i hi hi'=> (hqb hYp hR hl hbc i hi (hI i hi)).2 hi'⟩,⟨HY',hqa hYq ha' hbc' hc,fun i hi=>(hqb hYq hR' hl' hbc' i hi (hI' i hi)).1,fun i hi hi'=>(hqb hYq hR' hl' hbc' i hi (hI' i hi)).2 hi'⟩, ?_⟩
 let x:=Q.cast d Z e n
 have he: Y-Y'=x+(t-a')+(b-b'):=by rw [hYp,hYq,show x=a-t from Eq.symm H₅]; abel
 have h5:0≤B*δ:=mul_nonneg hB hδ;let p0:=A*ξ*Carrier.unitStep P.L+F W*(B*δ+0);have h6: 0≤p0:=by unfold p0; positivity
 let S:=z W*c*δ; let T':=u W*B*δ;have h7:0 ≤ S:=mul_nonneg (mul_nonneg hz' hc) hδ;have h8:0 ≤ T':=mul_nonneg (mul_nonneg hu' hB) hδ
 constructor
 · rw [he];apply (((hx'.add hX.switch h6 h7).add H₂.switch (add_nonneg h6 h7) h8)).mono le_rfl le_rfl (fun _=>le_rfl)
   change A*ξ*Carrier.unitStep P.L+F W* (B*δ+0)+z W*c*δ+u W*B*δ ≤ A*ξ/g+J W*(B+c)*δ
   rw [div_eq_mul_inv,add_zero]; change A*ξ*g⁻¹+_+z W*c*δ+u W*B*δ ≤ A*ξ*g⁻¹+_
   nlinarith only [mul_le_mul_of_nonneg_right hE h5,mul_le_mul_of_nonneg_right (show z W ≤ J W from (le_add_of_nonneg_left hu').trans hz0) (mul_nonneg hc hδ)]
 intro i hi;have hn:n≤d:=hi ▸ octave_le i
 let V(F:Pack n E):=Trill.pix X i.ear i.test.play F
 have hxa : Ready D G n (x + (t-a')) := by
   simpa only [one_smul] using Ready.two (1:ℝ) hR'' (Ready.minus hr0 hR')
 have h9: V Y-V Y'=V x+V (t-a')+V (b-b'):=by
   unfold V
   rw [←pix_minus X HY HY',he,pix_plus X hxa (Ready.minus hl hl'),pix_plus X hR'' (Ready.minus hr0 hR')]
 have h2:=hP i n hn _ (Ready.minus hr0 hR').coherent _ h7 hX.switch;have h3:= hP i n hn _ (Ready.minus hl hl').coherent _ h8 H₂.switch
 change |V Y-V Y'| ≤_;rw [h9];apply (abs_add_le ..).trans (le_trans (add_le_add ((abs_add_le ..).trans (add_le_add (hI'' i hi|>.1) h2)) h3) ?_)
 change A*0*g^(d-0)+F W*(B*δ)+p*(z W*c*δ)+p*(u W*B*δ)≤J W*(B+c)*δ
 have h3:F W+p*u W≤J W:= hE'
 have h4:p*z W ≤J W:=by nlinarith only [hp,hF0,hE'',hu',hz']
 nlinarith only [mul_le_mul_of_nonneg_right h3 h5,mul_le_mul_of_nonneg_right h4 (mul_nonneg hc hδ)]
end YM.RG08.Necks
