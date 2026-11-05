import YM.UVExtension.Lamppost.Fulcrum
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Filter Set Complex MeasureTheory Topology Metric
open scoped ContDiff BigOperators Classical
variable {r v : ℝ} {ι : Type} [Fintype ι]

lemma rolling (h:0<r) (hp:r≤v) (N:ℕ): ∃ K:ℝ,1≤K∧ ∀ (f:Plot ι→ℂ) (U q w:ℝ) (S : Set (Plot ι)),IsOpen S→ v<q → (∀ x:Plot ι,(∀ i,‖x i‖≤q)→ x∈S)→ Bumps S f→ 0 ≤ U→ (∀ x∈S, ‖f x‖≤U) →
    0 ≤ w → (∀ x: ι→ℝ,(∀ i, |x i| < r)→ ‖f (hoist x)‖ ≤w)→ U*(v/q)^N*(1-v/q)⁻¹≤w→∀ z:Plot ι, (∀ i,‖z i‖≤v)→ ‖f z‖≤ K^(Fintype.card ι)*w:=by
  obtain ⟨K,hK,H⟩:= rations N h hp; refine ⟨K,hK,fun f U q w S hS hv hq hf hU ht hw he hi=>?_⟩
  have hk(s:Finset ι):∀ z:Plot ι, (∀ i,‖z i‖≤v)→ (∀ i∉s,∃ x:ℝ,|x|<r∧z i=↑x)→ ‖f z‖ ≤ K^(s.card)*w:= by
    induction s using Finset.induction_on with
    | empty =>
      intro z hy hn; choose x hx hz using fun i=> hn i (by simp); simpa only [show z=hoist x from funext hz,Finset.card_empty,pow_zero,one_mul] using! he x hx
    | insert i s hJ hh =>
      intro z hx hy; let V:= Function.update z i; let r:=V ⁻¹' S
      have he : Differentiable ℂ V:= by
        intro t; apply differentiableAt_pi.mpr; intro j; by_cases h:i=j; subst j; simp only [V,Function.update_self]; exact differentiableAt_id
        simp only [V, Function.update_of_ne (Ne.symm h)]; exact differentiableAt_const (𝕜:=ℂ) _
      let Y:= K^s.card*w; have hF: w≤Y:= le_mul_of_one_le_left hw (one_le_pow₀ hK)
      have h' (t:ℂ)(ht:‖t‖≤v):∀ j, ‖V t j‖≤v:= by intro j; by_cases hz:j=i; simpa [V,hz]; simpa [V,hz] using hx j
      have hR (t:ℂ)(hp:t ∈ closedBall 0 q): t∈ r := by
        have ht':‖t‖ ≤ q:= mem_closedBall_zero_iff.mp hp
        apply hq (V t); intro j; by_cases h:j=i; simpa [V,h] using ht'; simpa [V,h] using (hx j|>.trans hv.le)
      have hU(q'): ‖q'‖ ≤ q→ ‖f (V q')‖≤U:= fun hz=> ht _ (hR q' (mem_closedBall_zero_iff.mpr hz))
      have hL:= H (f ∘ V) U q Y (by assumption) (hw.trans hF) hv ((hf r V (hS.preimage he.continuous) (fun _ hz=> hz) he.differentiableOn).mono (fun i hi=> hR i hi)) hU (by
        intro t hb; refine hh _ (h' _ ?_) ?_
        · exact (norm_real t|>.trans_le (hb.le.trans hp))
        intro j hj; by_cases h:j=i; subst j; exact ⟨t,hb,Function.update_self ..⟩
        rw [show V _ j=z j from Function.update_of_ne h _ _]; exact hy _ (by simp [h,hj])) (hi.trans hF) (z i) (hx i)
      simpa only [Function.comp_apply,V,Function.update_eq_self,Finset.card_insert_of_notMem hJ,pow_succ',mul_assoc,Y] using hL
  exact fun z hz=> by simpa using hk Finset.univ z hz (by simp)

abbrev BoxR (ι:Type) (r:ℝ) := { x:ι→ℝ // ∀ i, |x i| < r }
def envelope (h:0<r) (hp:r≤v) : Opening (BoxR ι r) (Plot ι) where
  call x:= hoist x.val
  span:= Courtyard (fun _=> ball 0 v)
  within x:= within.mpr (fun i=> by rw [mem_ball_zero_iff]; exact (norm_real _|>.trans_lt ((x.2 i).trans_le hp)))
  agrees f g hf hg hh:= matched (fun _=> ball 0 r) (c:=fun _=>0) (fun _=> ball_mem_nhds _ h) (fun _ t ht=> mem_ball_zero_iff.mpr (norm_real _|>.trans_lt ((mem_ball_zero_iff.mp ht).trans_le hp))) (fun _=> isOpen_ball) (fun _=> (convex_ball (0:ℂ) v).isPreconnected) hf hg (fun x hx=> hh ⟨x,fun i=> mem_ball_zero_iff.mp (hx i)⟩)

section charts
variable {A X D E : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (h:0<r) (hp:r≤v) (M:Opening D X) (P:Meter A E) (e:Plot ι→ X)
    (S:BoxR ι r → D)(hm:∀ f,M.call (S f)=e (hoist f.val)) (hs:IsOpen M.span) (he : Differentiable ℂ e)
-- universal analytic price migration to calibrated patch
include he S hm hs
variable {s:D→ P.Slot}
omit hs in
lemma sash {U q:ℝ} (H:Atlas P M s (fun _=> U)) (hv:v<q)(hR:∀ x:Plot ι,(∀ i, ‖x i‖≤q)→ e x∈M.span) : Nonempty (Atlas P (envelope h hp) (fun i=>s (S i)) (fun _ : Plot ι=> U)):= by
  let f z:= H.f (e z)
  have hv' : MapsTo e (envelope (ι:=ι) h hp).span M.span:= fun x hx=> hR x fun i=> ((mem_ball_zero_iff.mp (within.mp hx i)).trans hv).le
  refine ⟨⟨f,fun d i k=> by change H.f (e (hoist d.val)) _ _= _; rw [← hm d]; exact H.exacts ..,fun i k W g h hh ht=> H.pulse i k W (fun x=> e (g x)) h (hv'.comp hh) (he.comp_differentiableOn ht),fun z hz=> H.bounds _ (hv' hz)⟩⟩

-- quantify K independent of everything incl G/output tests. 
omit hs he S hm
def luck (N:ℕ) (ι : Type) [Fintype ι] := (rolling (ι:=ι) h hp N).choose
lemma luck_ge (N:ℕ)(ι:Type)[Fintype ι]:1≤luck h hp N ι:= (rolling (ι:=ι) h hp N).choose_spec.1
lemma setK (N:ℕ) : let K:=luck h hp N ι; ∀ (U q w:ℝ) (e:Plot ι→ X) (S:BoxR ι r→ D), (∀ f,M.call (S f)=e (hoist f.val))→ IsOpen M.span→ Differentiable ℂ e → v< q → (∀ x:Plot ι,(∀ i, ‖x i‖≤q)→ e x∈ M.span)→∀ (s:D→P.Slot) (_H:Atlas P M s (fun _=>U)), 0≤U→ 0≤w→ (∀ d,P.MeasureP (s (S d)) w)→ U*(v/q)^N*(1-v/q)⁻¹≤w→ Nonempty (Atlas P (envelope h hp) (fun i=>s (S i)) (fun _=>2*K^(Fintype.card ι)*w)) := by -- K existence order adjust later
  intro K U q w e S hm hs he hv hR s H hg hw ht hx
  have X':= (rolling (ι:=ι) h hp N).choose_spec.2
  obtain ⟨F⟩:= sash h hp M P e S hm he H hv hR
  refine ⟨⟨F.f,F.exacts,F.pulse,fun z hz=>?_⟩⟩
  rw [show 2*K^(Fintype.card ι)*w=K^(Fintype.card ι)*w +K^(Fintype.card ι)*w by ring]; apply P.c_clips
  intro i
  let f (v:X):= Meter.Finger.issue P i (H.f v)
  let p:= e ⁻¹' M.span; have he' : Bumps p (f ∘ e):=fun s g h hh ht=> P.pollen H.pulse i _ (fun x=> e (g x)) h (mapsTo_preimage e _|>.comp hh) (he.comp_differentiableOn ht)
  rw [show Meter.Finger.issue P i (F.f z)=f (e z) from ?_]
  swap
  · apply (envelope (ι:=ι) h hp).agrees (fun z=> Meter.Finger.issue P i (F.f z)) (f ∘ e) (P.pollen F.pulse i) (fun s g h hh ht=> he' s g h (fun x hx=> hR _ fun j=> ((mem_ball_zero_iff.mp (within.mp (hh hx) j)).trans hv).le) ht) (fun j=> ?_) hz
    unfold Function.comp; change Meter.Finger.issue P i (F.f _) = f (e (hoist j.val)); rw [← hm]; apply congr_arg (Meter.Finger.issue P i); funext v k; rw [F.exacts,H.exacts]
  refine X' (f ∘ e) U q w p (hs.preimage he.continuous) hv hR he' hg (fun z hz=> P.spare (H.bounds _ hz) i) hw (fun x hm' => ?_) hx _ (fun j=> (mem_ball_zero_iff.mp (within.mp hz j)).le)
  let d:BoxR ι r:=⟨x,hm'⟩; unfold Function.comp f; rw [← show M.call (S d)= _ from hm d, ← P.income i (w:= s (S d)) (fun _ _=> (H.exacts ..).symm),Complex.norm_real]; exact P.fare (ht d) i
end charts
end YM.UVExtension.Lamppost
