import YM.TraceExtension.Pith.Wall
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pith
open Function Filter Set Extraction Ward Climb Spec Over Pilot Table Analysis Maxwell StressFlux Work Work.A05 MeasureTheory Next.UVStress Spin
open scoped Topology BigOperators InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{p:Extraction.Order}{S:Table C.book}(H:(Bel C.book).Hierarchy){n:ℕ}
local notation "F₀" => Bel C.book
variable (F: Spec.Final C p S)(h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}
local instance (n:ℕ): ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
include h H in
lemma free_flair (x:Points (n+1))(hx:x∈conf _) (χ:E4→ℝ)(he:Window x χ)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4)(b:Axis):
    ∑ i, said x χ i (standard4 C) b Y v= pron b Y v x 1:=by
    obtain ⟨T,hT,h1,hK⟩:= Litpay (C:=C) h; obtain ⟨w,hw⟩:= hK.flux
    let v0:Fin n→(Bel C.book).Tag:= fun i=>⟨4,v i⟩
    have hz:shellGrad (Bel C.book) (standard4 C) χ b x v0 Y = pron b Y v x 1:=by
       rw [show standard4 C=T.T.J from hT.symm, hw.translation hx v0 he, strains T.T.W H T.lit.pales x hx b Y v one_pos]; simp only[one_smul,Complex.ofReal_one,one_mul]; exact (Work.A05.frontRead_at ..).symm
    rw [← hz]; simp only[said,Finset.sum_neg_distrib]; unfold shellGrad; congr! 1; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [sheet,Work.A05.weight,mul_one,one_smul,disc];rfl

-- determined test square at cap four. Precision of columns is just what's
-- needed for trace through first possible grade, no need to purchase a at
-- that loop order as well.
variable {P:ℝ→change S 4}
abbrev dial (C:Family G):=fun _:Fin 1=> stepField C
def E (P: ℝ→change S 4)(t:ℝ):= divRead (C:=C) sail (dial C) (standard4 C) timeAxis t (P t)
def B (P: ℝ→change S 4)(t:ℝ):= divRead (C:=C) sail (dial C) (erase (C:=C) (stepField C)) timeAxis t (P t)
def R (P: ℝ→change S 4)(χ:E4→ℝ)(t:ℝ):= flair (C:=C) sail χ (standard4 C) timeAxis (stepField C) (dial C) t (P t)
def Q (P: ℝ→change S 4)(χ:E4→ℝ)(t:ℝ):= flair (C:=C) sail χ (erase (C:=C) (stepField C)) timeAxis (stepField C) (dial C) t (P t)

def datum (C:Family G):= pron timeAxis (stepField C) (dial C) sail 1
def prism (C:Family G)(χ:E4→ℝ):= ∑ i, said sail χ i (erase (C:=C) (stepField C)) timeAxis (stepField C) (dial C)
lemma sail_at : sail ∈ conf _:=by simpa only [one_smul] using sail_on one_pos
include F h H
lemma station_limits(hP:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)(χ:E4→ℝ)(he: Window sail χ): Tendsto (R P χ) trail (𝓝 (datum C)) ∧ Tendsto (B (C:=C) P) trail (𝓝 (datum C)) ∧ Tendsto (Q P χ) trail (𝓝 (prism C χ)):=by
    let K:= F.room.kernel; let s:= stepField C; let v:= dial C
    refine ⟨?_,((stripes K H hP timeAxis s v sail sail_at).congr' ?_),tendsto_finsetSum _ (fun i _=> steps K H hP sail sail_at he i (erase (C:=C) s) timeAxis s v)⟩
    · rw [show datum C= _ from (free_flair H h _ sail_at χ he s v timeAxis).symm]; exact tendsto_finsetSum _ (fun i _=>steps K H hP sail sail_at he i (standard4 C) timeAxis s v)
    exact (show ∀ᶠ t:ℝ in trail,0<t from self_mem_nhdsWithin).mono fun i hi=>(div_cross F sail sail_at hi v s timeAxis).symm
variable {u d:ℝ→ℝ}(hg: Coupling G u)(hd:TendC F P d)(hP:PlotX F H 𝓛 h P)
include hg hd hP
lemma postd : Tendsto d trail (𝓝 0):=by
    have hx:= (hd.measures _ hg).mul ((hg.conforms h).pow 2); have he:Tendsto (fun i=>(d i/u i^ (2:ℕ))*u i^2) trail (𝓝 0):= by simpa using! hx
    apply he.congr'; filter_upwards[hg.positive] with i hi; rw [div_mul_cancel₀ _ (pow_ne_zero _ hi.ne')]
lemma promo : ∃ (a e:ℝ→ℝ), ∀ᶠ s in trail, Measures F s (P s) (a s) (d s) (e s):=by
    let Θ(s:ℝ)(c:ℝ×ℝ):= Measures F s (P s) c.1 (d s) c.2; let f(s:ℝ):=if he:∃ c:ℝ×ℝ,Θ s c then he.choose else 0
    refine ⟨Prod.fst ∘ f,Prod.snd ∘ f,?_⟩; filter_upwards[hd.tensor] with i hi
    have he:∃ c,Θ i c:=by obtain ⟨a,e,hp⟩:=hi; refine ⟨(a,e),{reads:=fun j k=>?_}⟩; rw[hp]; dsimp only; by_cases hv:j=k<;> simp[erase,hv,add_assoc]
    change Θ i (f i); unfold f; rw [dif_pos he]; exact he.choose_spec

/-- Exact determining Ward tests, units elided by this unselected square. -/
structure LiveP(P:ℝ→change S 4)(a d:ℝ→ℝ)(χ:E4→ℝ):Prop where
   normalization : ∀ᶠ t in trail,a t • R P χ t+d t • Q P χ t=B (C:=C) P t
   conservation : ∀ᶠ t in trail,a t • E P t + d t • B P t=0

omit hg hd H F hP h in
lemma amp (P:ℝ→change S 4)(χ:E4→ℝ)(s a:ℝ):a • R (C:=C) P χ s= (↑a:ℂ)* R P χ s:= Complex.real_smul ..
lemma lift_ward {a e:ℝ→ℝ}(ht:∀ᶠ s in trail,Measures F s (P s) (a s) (d s) (e s))(χ:E4→ℝ)(he:Window sail χ): LiveP (C:=C) P a d χ:=by
    constructor
    · filter_upwards[ht,self_mem_nhdsWithin,hP] with s hT hQ hi; exact (translates F hT sail sail_at hQ he hi.1.frame.align.unit timeAxis (stepField C) (dial C)).trans (div_cross F sail sail_at hQ (dial C) _ _).symm
    filter_upwards[ht,self_mem_nhdsWithin,hP] with s hs he hp using conserv F hs _ sail_at he hp.1.frame.align.unit (dial C) timeAxis

lemma akela {a:ℝ→ℝ}{χ:E4→ℝ}(he:Window sail χ)(ht:LiveP (C:=C) P a d χ)(hv:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m): Tendsto a trail (𝓝 1):=by
    obtain ⟨hr,hB,hQ⟩:= station_limits H F h hv _ he
    have hx:= (postd H F h hg hd hP).smul hQ; rw[zero_smul] at hx
    let r:= R (C:=C) P χ; let w:= datum C; have hp : w≠0:= sail_b H h
    have hz:Tendsto (fun t=> (a t:ℂ)*r t) trail (𝓝 w):=by
       have hs:= hB.sub hx; rw[sub_zero] at hs; exact hs.congr' (ht.normalization.mono (fun i hi=> ((eq_sub_of_add_eq hi).symm.trans (Complex.real_smul ..))))
    have hf:= hz.div hr hp; rw[div_self hp] at hf
    have hh:Tendsto (fun i=>(a i:ℂ)) trail (𝓝 1):= hf.congr' ((hr.eventually_ne hp).mono (fun i hi=>mul_div_cancel_right₀ _ hi))
    exact Complex.continuous_re.continuousAt.tendsto.comp hh

lemma eid {a:ℝ→ℝ}{χ:E4→ℝ}(he:Window sail χ)(ht: LiveP (C:=C) P a d χ)(hv:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m): Tendsto (fun s=>(u s^ (2:ℕ))⁻¹ • E P s) trail (𝓝 ((-d2 G) • datum C)):=by
    obtain ⟨hr,hB,hQ⟩:= station_limits H F h hv _ he; have hp:Tendsto (fun s=> d s / u s^ (2:ℕ)) trail (𝓝 (d2 G)):=by rw[force_b];exact hd.measures _ hg
    have ha:=akela H F h hg hd hP he ht hv; have hx:= ((hp.div ha one_ne_zero).neg).smul hB; rw[div_one] at hx
    refine hx.congr' ?_; filter_upwards [ht.conservation,ha.eventually_ne one_ne_zero,hg.positive] with t hh he hU
    have ht:(a t) • E P t= -(d t • B P t):= eq_neg_of_add_eq_zero_left hh
    change -(d t/ u t^2/a t) • B P t=_
    apply smul_right_injective _ he
    dsimp only; rw [smul_comm (a t) (u t^2)⁻¹, ht,smul_neg,neg_smul,smul_neg]; congr 1; rw [smul_smul, smul_smul]; congr 1; field_simp
end YM.Trace.Pith
