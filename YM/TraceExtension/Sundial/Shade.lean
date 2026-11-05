import YM.TraceExtension.Sundial.Plume

/-! Choose both scalar positions by the small determining X-square.
 No exact stress labels used in these normalization tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "Act"=> (Bel C.book).Field 4
variable {P P':ℝ→change S 4}(hP:PlotX F H 𝓛 h P)(hQ:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)
variable {χ:E4→ℝ}(hc:Window sail χ)

structure ShellNorm (P':ℝ→change S 4) (χ:E4→ℝ): Prop where
    valid:Window sail χ
    swings: ∀ᶠ t in trail,(R P' χ t).re=(datum C).re ∧ (B P' t).re=(datum C).re
structure Posed (P P':ℝ→change S 4) (x y:ℝ→ℝ):Prop where
    positiveX :∀ᶠ t in trail,0 < x t ∧ 0 < y t
    polls : ∀ᶠ t in trail, Tilt H h (P t) (P' t) (x t) (y t)
include H h in
lemma dato : (datum C).re≠0:=by
    by_contra hz; apply sail_b H h; change datum C=0; apply Complex.ext
    · exact hz
    unfold datum Pith.dial; rw[sails_peak H];rfl
include F hp hP hQ
include hc
lemma spectrum_s : ∃ (P':ℝ→change S 4)(x y:ℝ→ℝ), Posed H h P P' x y∧ ShellNorm P' χ:=by
    obtain ⟨R',B',hE⟩:= station_limits H F h hQ _ hc
    let b:=(datum C).re; let f(t:ℝ):=(R P χ t).re; let g(t:ℝ):=(B P t).re
    have he:Tendsto f trail (𝓝 b):= Complex.continuous_re.continuousAt.tendsto.comp R';have hv:Tendsto g trail (𝓝 b):= Complex.continuous_re.continuousAt.tendsto.comp B'
    let x(i):= Real.sqrt (b/g i); let y(t):= b/(x t*x t*f t); have hb:b≠0:=dato H h
    have hk:Tendsto (fun i=>b/g i) trail (𝓝 1):=by simpa only[div_self hb] using! (tendsto_const_nhds (x:=b)).div hv hb
    have hx:Tendsto x trail (𝓝 1):=by simpa [x] using hk.sqrt
    have hY:Tendsto y trail (𝓝 1):=by simpa only[y,one_mul,div_self hb] using! ((tendsto_const_nhds (x:=b)).div ((hx.mul hx).mul he) (by rw[one_mul,one_mul]; exact hb))
    let p'(i):= if H':x i≠0 ∧ y i≠0 then (elven H h (x i) (y i) H'.1 H'.2).trans (P i) else P i
    have hw :∀ᶠ i in trail,0<x i ∧ 0< y i:= (hx.eventually (lt_mem_nhds zero_lt_one)).and (hY.eventually (lt_mem_nhds zero_lt_one)); have ht:Posed H h P p' x y:=⟨hw,hw.mono (fun i hi=> ⟨fun v=> by unfold p'; rw [dif_pos ⟨(show 0<x i from hi.1).ne', (show 0<y i from hi.2).ne'⟩];rfl⟩)⟩
    refine ⟨p',x,y,ht,hc,?_⟩; filter_upwards [ht.polls,self_mem_nhdsWithin,hk.eventually (lt_mem_nhds zero_lt_one), he.eventually_ne hb,hv.eventually_ne hb,hw] with i hi hr hσ hu hz hV
    obtain ⟨hh,h'⟩:= total_p F H h hp _ _ hi i hr
    obtain ⟨hR,hQ⟩:= shells F H h hp _ _ hi χ i;
    rw [show R p' χ i=(y i*x i*x i) • R P χ i from hR,show B p' i=(x i*x i) • B P i from h']; simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; change y i*x i*x i*f i=b ∧ x i*x i*g i=b
    refine ⟨?_,?_⟩
    · have hA:x i≠0:= hV.1.ne'
      unfold y; field_simp
    rw[← pow_two,show x i ^ 2 = b/g i from Real.sq_sqrt (le_of_lt (show 0<b/g i from hσ)),div_mul_cancel₀ _ hz]
variable {x y:ℝ→ℝ}
omit hc hP hQ hp in
lemma Posed.eq (p:Posed H h P P' x y): ∀ᶠ i in trail,∃ (hx:x i≠0) (hy:y i≠0), P' i=(elven H h (x i) (y i) hx hy).trans (P i):=by
    filter_upwards [p.positiveX,p.polls] with i hi hp; exact ⟨hi.1.ne', hi.2.ne', LinearEquiv.ext fun v=> hp.portrait _⟩
variable (p:Posed H h P P' x y)(q: ShellNorm P' χ)
include p q
lemma anneal: Tendsto x trail (𝓝 1)∧ Tendsto y trail (𝓝 1):=by
    obtain ⟨hR,hB,hW⟩:= station_limits H F h hQ χ hc; let b:=(datum C).re; have he:= Complex.continuous_re.continuousAt.tendsto.comp hR; have hv:= Complex.continuous_re.continuousAt.tendsto.comp hB; have hb:=dato H h
    let f(i):= (R P χ i).re; let g(i):=(B P i).re; have ht :∀ᶠ i in trail, y i*x i*x i*f i=b ∧ x i*x i*g i=b:=by
       filter_upwards [p.polls,q.swings,self_mem_nhdsWithin] with i hi hq hv; rw [show R P' χ i=(y i*x i*x i) • R P χ i from (shells F H h hp (P i) _ hi χ i).1, show B P' i=(x i*x i) • B P i from (total_p F H h hp (P i) _ hi i hv).2] at hq; simpa only[Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hq
    have hX:Tendsto (fun i=>x i^2) trail (𝓝 1):=by
        have hp:Tendsto (fun i=> b/g i) trail (𝓝 1):=by simpa only[div_self (show b≠0 from hb)] using! (tendsto_const_nhds (x:=b)).div (show Tendsto g trail (𝓝 b) from hv) hb
        apply hp.congr'; filter_upwards [ht,hv.eventually_ne hb] with i hi he; rw [div_eq_iff (show g i≠0 from he),pow_two,hi.2]
    have hx:Tendsto x trail (𝓝 1):=by
       have hh:= hX.sqrt; rw [Real.sqrt_one] at hh; refine hh.congr' (p.positiveX.mono fun i hi=> Real.sqrt_sq hi.1.le)
    refine ⟨hx,?_⟩; have hw:= hx.mul hx|>.mul (show Tendsto f trail (𝓝 b) from he); rw[one_mul,one_mul] at hw
    have hp:= (tendsto_const_nhds (x:=b)).div hw hb; rw [div_self hb] at hp; apply hp.congr'; filter_upwards[ht, hw.eventually_ne hb] with i hi hu; change b/(x i*x i*f i)=y i; rw [div_eq_iff hu, ← mul_assoc,← mul_assoc, hi.1]
lemma avatar : Another F (H:=H) P' P:=by
    obtain ⟨hx,hy⟩:= anneal F H h hp hP hQ hc p q
    constructor
    · filter_upwards [p.eq F H h,hP] with i hi hu; obtain ⟨u,v,hE⟩:=hi; rw[hE]; exact elder F H h hu.1.frame _ _ u v
    have h₁:Tendsto (fun i=> (x i)⁻¹) trail (𝓝 1):=by simpa using! hx.inv₀ one_ne_zero
    have h₂:Tendsto (fun i=> (y i)⁻¹) trail (𝓝 1):=by simpa using! hy.inv₀ one_ne_zero
    refine (esprit H h h₁ h₂).congr' ?_; filter_upwards [p.eq F H h] with i hi; obtain ⟨u,v,hE⟩:= hi; rw[hE]; ext1 w; let Z:=elven H h (x i) (y i) u v; change _=Z.symm ((P i).symm (P i w));rw[LinearEquiv.symm_apply_apply];rfl
lemma ethane:Pith.E P'=ᶠ[trail] fun i=> (y i*x i) • Pith.E P i:= (p.polls.and self_mem_nhdsWithin).mono fun i ⟨hi,hu⟩=> (total_p F H h hp (P i) _ hi i hu).1
lemma crystals:Tendsto (Pith.Q P' χ) trail (𝓝 (prism C χ)):=by
    obtain ⟨hx,he⟩:= anneal F H h hp hP hQ hc p q
    have hh:= (hx.mul hx|>.mul hx).smul ((station_limits H F h hQ χ hc).2.2);rw[one_mul,one_mul,one_smul] at hh; exact hh.congr' (p.polls.mono (fun i hi=> (shells F H h hp (P i) _ hi χ i).2.symm))
end YM.Trace.Sundial
