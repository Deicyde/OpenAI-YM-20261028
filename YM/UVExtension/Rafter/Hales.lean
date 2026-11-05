import YM.UVExtension.Rafter.Plier
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice RG Topology Set Push.AbsoluteSums Metric BoundedContinuousFunction
open Lamppost Eyelet
open scoped BigOperators Classical
variable {A B D C C' Z E U : Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    {P : Meter.{0,0,0} A B}{Q:Meter.{0,0,0} C C'}{T:Opening D Z}{r g:D→P.CSlot}{a b x:ℝ}
open Meter
namespace Stalk
lemma ascend {f:D→P.Slot}(F:Atlas P T f (fun _=>a)) : Stalk P T (fun i j v=> ↑(f i j v)) a:=⟨_,F.pulse,fun d=> by ext1 i; exact funext (fun x=> F.exacts d i x), F.bounds⟩
lemma plus (h:Stalk P T r a)(hp:Stalk P T g b): Stalk P T (fun d i j=> r d i j+g d i j) (a+b):=by
   obtain ⟨f,hf,hR,hT⟩:=h.rises; obtain ⟨p,hp,hq,hV⟩:=hp.rises
   refine ⟨fun z i j=> f z i j+p z i j, fun i j=> bends_add (hf i j) (hp i j),fun i=>?_ ,fun z hz=>?_ ⟩
   · dsimp only; rw [hR,hq]
   obtain ⟨v,hv,hV'⟩:= (hT z hz).afloat; obtain ⟨d,he,hA⟩:= (hV z hz).afloat
   exact ⟨fun i=> v i+d i,fun i=>⟨add_nonneg (hv i).1 (he i).1,fun j=>(norm_add_le ..).trans (add_le_add ((hv i).2 j) ((he i).2 j))⟩,fun i=>by simpa only [mul_add] using budget_plus (hV' i) (hA i)⟩
lemma scales (h:Stalk P T r a)(b:ℂ): Stalk P T (fun d i j=> b*r d i j) (‖b‖*a):=by
   obtain ⟨f,hf,hR,hT⟩:=h.rises; refine ⟨fun z i j=> b*f z i j, fun i j _ _ w x g=> DifferentiableOn.const_mul (hf i j _ _ w x g) b,fun i=>?_ ,fun z hz=>?_ ⟩; · dsimp only; rw [hR]
   obtain ⟨v,hv,hV⟩:= (hT z hz).afloat; refine ⟨fun i=> ‖b‖ * v i,fun i=>⟨mul_nonneg (norm_nonneg _) (hv i).1,fun j=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left ((hv i).2 j) (norm_nonneg _))⟩,fun i=>?_⟩
   simpa only [mul_left_comm ‖b‖] using! budget_scale (norm_nonneg b) (hV i)
lemma directs (h:Stalk P T r a)(w:D→ Q.CSlot)(hp:∀ (S:Finset D)(p:D→ℂ) (c:ℝ), 0≤c→ P.MeasureP (fun i k=>∑ j∈S,p j*r j i k) c→ Q.MeasureP (fun i k=> ∑ j∈S,p j*w j i k) (x*c)) (hx:0≤x)(ha:0≤a): Stalk Q T w (4*x*a):=by
   have hg (t:Q.Finger):∃ f:Z→ℂ, Bumps T.span f∧(∀ d,f (T.call d)=Finger.issue Q t (w d))∧∀ z∈ T.span, ‖f z‖≤ 2*x*a:=by
     refine sprigs h ha hx _ (fun S p c hc hV=>?_); have hv:= Meter.spare Q (hp S p c hc hV) t; rw [combines] at hv; exact hv
   choose f hf hF hT using hg; choose p hP using Q.awake
   have ht {r:Q.CSlot}(i k)(b): Finger.issue Q (Q.single i k b) r=(Q.cost b i:ℂ)*r i k:=by
      unfold Finger.issue Meter.padding; -- pick private! need lemma via re/im sel. simp? private reducible
      simp only [Meter.single,Finset.sum_singleton]; rw [show Complex.ofReal 1=(1:ℂ) from Complex.ofReal_one, mul_one]; congr 1
      change Option.elim' 0 (r i) (if h:i=i then some k else none) = _; simp
      -- unfold pick inaccessible -> alternative via h? 
   let g(z:Z)(i:C)(k:Q.test i):= (Q.cost (p i) i:ℂ)⁻¹ * f (Q.single i k (p i)) z
   have hG i k : Bumps T.span (fun z=> g z i k):=fun _ _ w h v=> DifferentiableOn.const_mul (hf _ _ _ w h v) _
   have H d:g (T.call d)=w d:=by
      ext1 i; funext k; unfold g; rw [hF,ht,inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hP i|>.ne'))]
   refine ⟨g,hG,H,fun z hz=>?_⟩; rw [show 4*x*a=2*x*a+2*x*a by ring]; apply Meter.c_clips
   intro t; apply Eq.trans_le (congr_arg norm (show Finger.issue Q t (g z)=f t z from ?_)) (hT _ _ hz)
   exact T.agrees (fun z=>Finger.issue Q t (g z)) (f t) (Q.pollen hG t) (hf t) (fun d=>by change Finger.issue ..=_; rw [H,hF]) hz
lemma eases (h:Stalk P T r a)(he:a ≤ b):Stalk P T r b:=by
   obtain ⟨f,hf,hR,hT⟩:=h.rises; refine ⟨f,hf,hR,fun z hz=>?_⟩; obtain ⟨v,hv,hV⟩:= (hT z hz).afloat; exact ⟨v,hv,fun i=> by exact ⟨(hV i).1,(hV i).2.1,(hV i).2.2.trans he⟩⟩
end Stalk
end YM.UVExtension.Rafter
