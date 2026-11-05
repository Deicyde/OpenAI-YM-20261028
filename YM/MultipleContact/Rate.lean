import YM.MultipleContact.Total
/-! Quantitative normal scaling-degree and extension estimates for integrated prescriptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Power
open Function Filter MeasureTheory Set TopologicalSpace Metric Table Direct Analysis Extraction
open scoped Topology BigOperators ContDiff Classical
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E]
 [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
variable {G : Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}
variable {B:Splitting P} {D:∀ h,Detector S h} {t:Target L}
variable {R:ℝ} {σ Hmax k k':ℕ} {A:Set (Target L)} {m:Option ℕ}
variable {Z Z':ℝ→Target L→(E→ℂ)→ℂ}

def Rate (p:ℝ)(k:ℕ)(A:Set (Target L))(Z:ℝ → Target L → (E → ℂ) → ℂ) : Prop:= ∀M> (0:ℝ),∃ c:ℝ, 0<c ∧ ∀t∈A,∀f:E → ℂ, ContDiff ℝ ∞ f → (∀ x,f x≠0 → ‖x‖≤M) → ∀ W,JetBounds k f W → ∀ s r:ℝ,0<r → r≤1 → r≤s → ‖Z s t (scaled r f)‖ ≤ c* W * r^p
namespace Rate
variable {p:ℝ} (hZ:Rate p k A Z)
omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
include hZ in
lemma sum (hZ':Rate p k A Z') : Rate p k A (fun s t f=>Z s t f+Z' s t f):=by
     intro M hM; obtain ⟨c,hc,h⟩:=hZ M hM
     obtain ⟨c',hc',q⟩:=hZ' M hM
     refine ⟨c+c',add_pos hc hc',fun t ht f hf hF W hW s r hr r' hr' =>?_⟩
     exact (norm_add_le ..).trans ((add_le_add (h t ht f hf hF W hW s r hr r' hr') (q t ht f hf hF W hW s r hr r' hr')).trans_eq (by ring))
omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma zeroR : Rate p k A (0 : ℝ→Target L→(E→ℂ)→ℂ):=fun M _=> ⟨1,one_pos,fun t ht f _ hf W hW s r hr _ _=> by rw [Pi.zero_apply,Pi.zero_apply,Pi.zero_apply,norm_zero]; have hv:=hW.1; positivity⟩
omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma sumRate {ι:Type*}{Y:ι→ℝ→Target L→(E→ℂ)→ℂ} (v:Finset ι)(h:∀i∈v,Rate p k A (Y i)):Rate p k A (fun s t f=>∑ i∈v,Y i s t f):=by
   induction v using Finset.induction_on with
   | empty=> simpa only [Finset.sum_empty,Pi.zero_def] using (zeroR (E:=E) (A:=A) (p:=p) (k:=k))
   | insert i v hi ih=>
        simp_rw [Finset.sum_insert hi]
        exact sum (h i (by simp)) (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
include hZ in
lemma weaker {q:ℝ}(hq:q≤p)(hk:k≤k'): Rate q k' A Z:=by
   intro M hM; obtain ⟨c,hc,hv⟩:=hZ M hM
   refine ⟨c,hc,fun t ht f hf hF W hW s r hr r' hr'=>?_⟩
   exact (hv t ht f hf hF W (hW.weaker hk) s r hr r' hr').trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr r' hq) (mul_nonneg hc.le hW.1))
end Rate
variable {V : Target L→E→ℂ}
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma mapField {F F':Type*}[NormedAddCommGroup F] [NormedAddCommGroup F'] [NormedSpace ℂ F][NormedSpace ℂ F'](L:F→L[ℂ] F') {v:E→F}{p c:ℝ}(hv:Kas R p c v):∃ c',Kas R p c' (L ∘ v):=by
     refine ⟨‖L‖ * c +1,by have he:=hv.pos; positivity, L.continuous.comp_aestronglyMeasurable hv.measurable,fun x hx hX=>?_⟩
     exact (L.le_opNorm ..).trans ((mul_le_mul_of_nonneg_left (hv.grow x hx hX) (norm_nonneg L)).trans (by nlinarith [Real.rpow_nonneg (norm_nonneg x) p]))

variable (hd:1≤ Module.finrank ℝ E) (H:Estimates P D σ Hmax R V A)
include H
lemma pieceOrd (i:ℕ)(hi:i≤k)(hk:k≤Hmax){ε:ℝ}(hε:0<ε) :∃ c,∀ t∈A, Kas R (-(σ:ℝ)-ε) c (piece B D V k i t):=by
   obtain ⟨c,hc⟩:=H.grow ε hε
   let h:=readPrice H hk hc; let g:=mapField (LinearMap.toContinuousLinearMap (B.part i k)) h.choose_spec
   obtain ⟨b,_,he⟩:=centerPrice H (hi.trans hk) g.choose_spec; exact ⟨b,he⟩
include hd
omit H in
lemma termRate {p γ:ℝ}{m:Option ℕ}{c:ℝ}(he:∀t∈A,Kas R p c (V t))(hc:0<γ)(hq: Direct.admissible m p γ (Module.finrank ℝ E)) {j:ℕ}(hj:price m≤j):
   Rate (p-γ) j A (fun s t f=> primary R s m V f t):=by
       intro M hM; let C:= (c * scaledCost m M p γ (Module.finrank ℝ E)* J (E:=E) (-(Module.finrank ℝ E:ℝ)+γ) R)
       let c' :=max 1 C; have hc': 0<c':=lt_of_lt_of_le zero_lt_one (le_max_left ..)
       refine ⟨c',hc',fun t ht f hf hF w hw s r hr hr' hr''=>?_⟩
       have h:=scaledTerm (K:=V t) hd (he t ht) hf hM hF (hw.weaker hj) hc hr hr'' hq
       let B := Module.finrank ℝ E
       have h':c * (scaledCost m M p γ B * w) * J (E:=E) (-(B:ℝ)+γ) R = C*w := by unfold B C;ring
       rw [h'] at h
       exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show C ≤ c' from le_max_right ..) hw.1) (by positivity :0≤r^(p-γ)))

lemma normal (hh:critical σ E≤Hmax){ε:ℝ}(hε: 0<ε):Rate (-(σ:ℝ)-ε) (1+σ) A (fun s=>rule B D R s σ V):=by
     let e:= min (ε/4) (1/4); have he:0<e:=lt_min (by linarith) (by norm_num)
     by_cases hk:Module.finrank ℝ E ≤ σ
     · set k:=critical σ E; have hx:k=σ-Module.finrank ℝ E:=rfl
       obtain ⟨c,γ,hγ,hv⟩:=H.signed k hh; let γ':=min γ (1/2)
       have hw:-(σ:ℝ) ≤ k-σ:=by linarith [Nat.cast_nonneg (α:=ℝ) k]
       let g:= fun s t f=> primary R s none (miss D k V) f t
       have h':Rate (-(σ:ℝ)-ε) (1+σ) A g:=by
         refine (termRate (m:=none) hd hv (show 0<γ' from lt_min hγ (by norm_num)) ?_ (j:=1+σ) (by simp [price])).weaker (by have he':γ'≤γ:=min_le_left ..; linarith only [hw,hε,he']) le_rfl
         rw [admissible]; change γ'≤_; have hw:= congr_arg (fun n:ℕ=>(n:ℝ)) hx
         rw [Nat.cast_sub (R:=ℝ) hk] at hw; have he':γ'≤γ:=min_le_left ..; linarith only [he',hw]
       have hpr(i:Fin (k+1)):price (some (k-i.val))≤1+σ:=by change (k-i.val)+1≤1+σ; omega
       let w(i:Fin (k+1)):=fun s t f=>primary R s (some (k-i.val)) (piece B D V k i.val) f t
       have hh':(k:ℝ)=σ-Module.finrank ℝ E :=by rw [hx];exact Nat.cast_sub hk
       suffices hu:∀i:Fin (k+1),Rate (-(σ:ℝ)-ε) (1+σ) A (w i) by
            rw [show (fun s=>rule B D R s σ V)=(fun s t f=> g s t f+∑ i:Fin (k+1),w i s t f) from funext fun s=>funext fun t=>funext fun f=>if_pos hk]
            exact Rate.sum h' (Rate.sumRate Finset.univ fun i _=>hu i)
       intro i; have hi:= Nat.le_of_lt_succ i.isLt
       by_cases hy:i.val=0
       · obtain ⟨c,hc⟩:=pieceOrd (B:=B) H i.val hi hh he
         refine (termRate hd hc he ?_ (j:=1+σ) (hpr i)).weaker (by linarith only [show e≤ε/4 from min_le_left (ε/4) (1/4),hε]) le_rfl
         dsimp only [admissible]; rw [Nat.cast_sub (R:=ℝ) hi,show (i.val:ℝ)=0 by exact_mod_cast hy]; unfold e at *; constructor
         · linarith only [hh',he]
         linarith only [hh',min_le_right (ε/4) ((1:ℝ)/4)]
       obtain ⟨c,γ,hγ,hγ',hv⟩:=piecePrice H B i.val hi hh
       obtain ⟨c,hc,hc'⟩:=centerPrice H (hi.trans hh) hv
       set q:= (i.val:ℝ); have hq': 0<γ/2:=by positivity
       refine (termRate hd (m:=some (k-i.val)) hc' hq' ?_ (hpr i)).weaker ?_ le_rfl
       · dsimp only [admissible]; rw [Nat.cast_sub (R:=ℝ) hi]
         dsimp [q] at *
         constructor <;> linarith only [hh',hγ',hγ]
       have hg:1≤q:=by dsimp [q]; exact_mod_cast (show (1:ℕ) ≤ i.val by omega)
       dsimp [q] at *; linarith only [hg,hε,hγ]
     obtain ⟨c,hc⟩:=H.grow e he; rw [show (fun s=> rule B D R s σ V)=fun s t f=>primary R s none V f t from funext fun s=>funext fun t=>funext fun f=>if_neg hk]
     refine Rate.weaker (termRate (m:=none) hd hc he ?_ (j:=1+σ) (by simp [price])) ?_ le_rfl
     · unfold admissible e; have hz : σ+1≤Module.finrank ℝ E:=by omega
       linarith only [min_le_right (ε/4) ((1:ℝ)/4),show (σ:ℝ)+1≤Module.finrank ℝ E by exact_mod_cast hz]
     exacts [by linarith only [min_le_left (ε/4) ((1:ℝ)/4),hε]]
end YM.MultipleContact.Power
