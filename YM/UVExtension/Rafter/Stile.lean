import YM.UVExtension.Rafter.Late
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Upswing
import YM.UVExtension.Crown.Tab
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Set Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Lamppost Concert Local MergeProof Planned.GuardedAtom Guard Rainfall Eyelet Source Next.Foundations Wet Extra.Histories
open PhysicalNext PhysicalNext.Repeat Linden Graces
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{d:ℕ}{ι J D Z:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    {T:Opening D Z}{V:Meter.{0} J Unit}{P:Meter.{0} ι Unit}
variable {v:D→ P.CSlot}{w:D→ V.CSlot}{a:ℝ}
lemma promote (p:ι ↪ J)(q: ∀ i, V.test (p i)→P.test i) (he:∀ d i k,w d (p i) k=v d i (q i k)) (hx:∀ i,i ∉ range p →∀ d k, w d i k=0) (hb:∀ i,V.cost () (p i) ≤ P.cost () i)(hp:Stalk P T v a): Stalk V T w a:=by
   obtain ⟨f,hf,hQ,h⟩:=hp.rises; let u (j:J)(h:j∈range p):= h.choose
   have hu (i:J)(h:i∈range p): p (u i h)=i:= h.choose_spec
   let t (z:Z): V.CSlot:= fun i x=> if h:i∈range p then f z (u i h) (q _ (hu i h|>.symm ▸ x)) else 0
   have hr z i x: t z (p i) x= f z i (q i x) := by
     let h: p i∈range p:= mem_range_self _; unfold t; rw [dif_pos h]
     suffices H:∀ (k:ι)(hk:p k=p i), f z k (q k (hk.symm ▸ x))= f z i (q i x) from H (u (p i) h) (hu _ h)
     intro k hk; have ha:=p.injective hk; subst k; rfl
   refine ⟨t,fun i x=> ?_,fun d=> ?_,fun z hz=> ?_⟩
   · unfold t; split; next => exact hf _ _
     exact bumps _ _ (differentiableOn_const _)
   · ext1 i; funext x; by_cases h:i∈range p; obtain ⟨i,rfl⟩:=h; rw [hr,hQ,he]
     unfold t; rw [dif_neg h,hx i h d x]
   obtain ⟨b,hb',hT⟩:= (h z hz).afloat; let u i:= Function.extend p b 0 i; have hl i:u (p i)=b i:= p.injective.extend_apply ..
   have hk i(h:i∉range p): u i=0:= Function.extend_apply' b (0:J→ℝ) i h
   have hV i: 0 ≤ u i:=by by_cases h:i∈range p; obtain ⟨i,rfl⟩:=h; rw [hl]; exact (hb' i).1; rw [hk i h]
   refine ⟨u,fun i=>⟨hV _,fun j=>?_⟩,fun x=>Local.sumBudget_pass p _ ?_ (fun i hi=>by rw [hk i hi,mul_zero])⟩
   · by_cases h:i∈range p; obtain ⟨i,rfl⟩:= h; rw [hr,hl]; exact (hb' i).2 _
     unfold t; rw [dif_neg h,norm_zero,hk _ h]
   simp_rw [hl]; exact budget_mono (hT ()) (fun i=>mul_nonneg (V.nonneg ..) (hb' i|>.1)) (fun i=>mul_le_mul_of_nonneg_right (hb i) (hb' i|>.1))

variable (p:BudgetPoint)(Y:ι→Support n)(Z':J→Support n)(ζ:ℂ)(F:D→ι→ Config G n→ℝ)(H:D→ι→ Config G n→ℝ)(C:D→J→ Config G n→ℂ)(e:ι↪J)(hc:∀ i j,C i (e j)= ζ • ((Complex.ofReal ∘ F i j)+ Complex.I • (Complex.ofReal ∘ H i j))) (hY:∀ i,Z' (e i)=Y i)
set_option quotPrecheck false
local notation "A!"=> (cardsP (G:=G) p 0 Y (p.supportExponent+2))
private lemma sums {X:Support n}{g:Config G n→ℂ}{f h: Config G n→ℝ}(hz:ζ≠0)(hg:g = ζ • ((Complex.ofReal ∘ f) + Complex.I • (Complex.ofReal ∘ h))) (he:p.Regular X g) (i:Tap p G 0 X): i.read g= ζ*(Complex.ofReal (i.read f) + Complex.I*Complex.ofReal (i.read h)):= by
    let q:= ζ⁻¹ • g; have hv:q=(Complex.ofReal ∘ f) + Complex.I • (Complex.ofReal ∘ h) :=by unfold q; rw [hg,smul_smul, inv_mul_cancel₀ hz,one_smul]
    have ht:f=Complex.reCLM ∘ q:=by rw [hv]; ext1 u; simp
    have hj:h=Complex.imCLM ∘ q:=by rw [hv]; ext1 u; simp
    have hp: p.Regular X q:=regular_smul _ he
    have hR(x:Config G n→ℝ)(hx:p.Regular X x) : i.read (Complex.ofReal ∘ x)=↑(i.read x):= Local.left_linear Complex.ofRealCLM i.poll (hx.smooth _ i.live) i.card
    have hw(x:Config G n→ℂ)(hx:p.Regular X x)(c:ℂ) : i.read (c • x)= c*i.read x:= Local.left_linear (c • ContinuousLinearMap.id ℝ ℂ) i.poll (hx.smooth _ i.live) i.card
    have hr:p.Regular X f:=by rw [ht]; exact readings _ hp
    have hI:p.Regular X h:=by rw [hj]; exact readings _ hp
    have hρ:=Blush.ornate hr; have hi:= Blush.ornate hI -- ns
    rw [hg,hw _ (regular_add hρ (regular_smul _ hi)), show i.read ((Complex.ofReal ∘ f)+Complex.I • (Complex.ofReal ∘ h))= i.read (Complex.ofReal ∘ f)+ i.read (Complex.I • (Complex.ofReal ∘ h)) from Local.left_add i.poll (hρ.smooth _ i.live) ((regular_smul _ hi).smooth _ i.live) i.card, hw _ hi,hR f hr,hR h hI]
include hc hY
lemma mist {b:ℝ}(hz:ζ≠0)(he:∀ i j,p.Regular (Z' j) (C i j))(hK:∀ j,j∉ Set.range e → ∀ i,C i j=0)(hp:Nonempty (Atlas (cardsP (G:=G) p 0 Y (p.supportExponent+2)) T (fun i j (k:Tap p G 0 (Y j))=> k.read (F i j)) (fun _=>a)))(hr:Nonempty (Atlas (cardsP (G:=G) p 0 Y (p.supportExponent+2)) T (fun i j (k:Tap p G 0 (Y j))=> k.read (H i j)) (fun _=>b))): Stalk (shop (G:=G) p Z') T (fun i j (k:Tap p G 0 (Z' j))=> k.read (C i j)) (‖ζ‖*(a+b)):=by
    obtain ⟨f⟩:= hp; obtain ⟨g⟩:=hr; have hg:= ((Stalk.ascend f).plus ((Stalk.ascend g).scales Complex.I)).scales ζ; rw [Complex.norm_I,one_mul] at hg
    apply promote e (fun j k=> (show Tap p G 0 (Y j) from hY j ▸ (show Tap p G 0 (Z' (e j)) from k))) ?_ ?_ ?_ hg
    · intro i j k; let u:Tap p G 0 (Z' (e j)):=k; have h:= sums p ζ hz (hc i j) (he ..) u -- HEq casts
      have H_ (q:Support n)(ht:Z' (e j)=q)(v :Config G n→ℝ): u.read v=(show Tap p G 0 q from ht ▸ u).read v:=by subst q;rfl
      rw [H_ _ (hY j) (F i j), H_ _ (hY j) (H i j)] at h
      exact h
    · intro j hj d k; let z:Tap p G 0 (Z' j):= k; change z.read (C d j)= _; rw [hK j hj]; simp [Tap.read,show (0:Config G n→ℂ)=(fun _=>0) from rfl, Work.G07.left_const]
    intro i; exact le_of_eq (by change Real.exp _=Copse.worth ..; unfold Copse.worth; rw [Copse.one,hY])
end YM.UVExtension.Rafter
