import YM.MultipleContact.TestBounds
import YM.MultipleContact.Rate

/-! Signed field-subtracted remainder on total Taylor sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Power
open Function Filter MeasureTheory Set TopologicalSpace Metric Table Direct Analysis Extraction
open scoped Topology BigOperators ContDiff Classical
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E] [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
variable {G : Gauge}{L:Register G}{S:Table L}{P:DiffPlan S}
variable {B:Splitting P} {D:∀ h,Detector S h}
variable {R:ℝ} {σ Hmax k:ℕ} {A:Set (Target L)} {m:Option ℕ}
variable {Y:Target L→E→ℂ}

def readAfter (D:∀ h,Detector S h)(k:ℕ) : (Target L→ℂ)→ₗ[ℂ] S.Field k := (D k).decode.comp (LinearMap.funLeft _ _ (fun e:(D k).probes=> (S,e.val)))
private def returner (D:∀ h,Detector S h)(k:ℕ) : (Target L→ℂ)→ₗ[ℂ](Target L→ℂ) := (LinearMap.id - LinearMap.pi (fun t=> (response t.1 k t.2).comp (readAfter D k)))
/-- OPE remainder using the same fixed detector system, tested against `t`. -/
def extMiss (B:Splitting P)(D:∀ h,Detector S h)(R s:ℝ)(σ h:ℕ)(Y:Target L→E→ℂ)(t:Target L)(f:E→ℂ):ℂ := returner D h (fun t=> rule B D R s σ Y t f) t

omit [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] [MeasureSpace E] in
private lemma returns (D:∀ h,Detector S h)(k:ℕ)(Z:Target L→E→ℂ)(x:E): returner D k (Z · x)=fun t=>miss D k Z t x :=rfl

variable (H:Estimates P D σ Hmax R Y A) (hd:1≤Module.finrank ℝ E)
include H
lemma read_mem {X:E→S.Field k}{h:ℕ}(hk:k≤h)(he:h≤Hmax)(x:E) : readField D (centerRead k X) h x = P.rise hk (X x):=by
   exact Eq.trans (congr_arg ((D h).decode) (funext fun i=> (H.inherit _ (H.active h he i) _ _ hk _).symm)) ((D h).fixes ..)
include hd
omit hd in
lemma miss_center_le {X:E→S.Field k}{h:ℕ}(hk:k≤h)(he:h≤Hmax)(t:Target L)(ht:t∈A)(x:E): miss D h (centerRead k X) t x=0:=by
   change response t.1 k t.2 (X x)- response t.1 h t.2 (_)=_
   rw [read_mem H hk he,H.inherit t ht k h hk,sub_self]
private lemma afterTerm {Z:Target L→E→ℂ} {h:ℕ} {m:Option ℕ} {s:ℝ}
   (hh:h≤Hmax)(hs:0<s)(a:Admitted A R m Z)(f:E→ℂ)(hf:ContDiff ℝ ∞ f)(hC:∃C,JetBounds (price m) f C) {t:Target L} (ht:t∈A):
     returner D h (primary R s m Z f) t = primary R s m (miss D h Z) f t:=by
   let v := fun (t:Target L)(x:E)=>diff s m f x • Z t x
   let U := (fun x:E=> fun i:(D h).probes=> v (S,i.val) x)
   let F: ((D h).probes→ℂ)→L[ℂ] ℂ := LinearMap.toContinuousLinearMap ((response t.1 h t.2).comp (D h).decode)
   have hv(i:(D h).probes): IntegrableOn ((U · i)) (ball 0 R) := Admitted.valid hd a s hs ⟨S,i.val⟩ (H.active h hh i) f hf hC
   have hg : IntegrableOn U (ball 0 R) := MeasureTheory.Integrable.of_eval hv
   have h' : IntegrableOn (fun x:E=>F (U x)) (ball 0 R):= by exact F.integrable_comp hg
   have hI(y):diff s m f y•(miss D h Z t y)=v t y-F (U y) := by
       change diff s m f y • (Z t y-response t.1 h t.2 ((D h).decode _))= _- response t.1 h t.2 ((D h).decode _)
       rw [smul_sub,← map_smul,← map_smul]; rfl
   dsimp only [returner,LinearMap.sub_apply,LinearMap.id_apply,LinearMap.comp_apply,LinearMap.pi_apply,Pi.sub_apply]
   unfold primary term; simp_rw [hI]; rw [integral_sub (Admitted.valid hd a s hs t ht f hf hC) h',F.integral_comp_comm hg]
   change _ - F (fun i=> ∫ (x:E) in ball 0 R,U x i) = (∫ (x:E) in ball 0 R,diff s m f x • Z t x)-F _; congr 2
   exact funext (fun i=>(eval_integral hv i).symm)

omit hd in
private lemma nested (h:ℕ)(hh:h≤Hmax)(hk:critical σ E≤h){t:Target L}(ht:t∈A): miss D h (miss D (critical σ E) Y) t=miss D h Y t:=by
   let k:=critical σ E; ext1 x
   change _- response t.1 h t.2 (readField D (miss D k Y) h x)=_
   rw [miss_read H hk hh,map_sub,H.inherit t ht k h hk]
   unfold miss centerRead; simp only [Pi.sub_apply]; abel

lemma afterHigh {h:ℕ} {s:ℝ}(hh:h≤Hmax)(hk:critical σ E≤h)(hs:0<s){f:E→ℂ}(hf:ContDiff ℝ ∞ f)(hc:∃C,JetBounds (1+σ) f C)(t:Target L)(ht:t∈A) : extMiss B D R s σ h Y t f = primary R s none (miss D h Y) f t:=by
   let k:=critical σ E
   unfold extMiss
   by_cases hd' : Module.finrank ℝ E ≤ σ
   · rw [show (fun t=> rule B D R s σ Y t f)=primary R s none (miss D k Y) f+(∑i:Fin (k+1), primary R s (some (k-i.val)) (piece B D Y k i.val) f) from by ext1 t; simp [rule,hd',k]]
     rw [map_add,map_sum,Pi.add_apply,Finset.sum_apply,afterTerm H hd hh hs (signedAdmitted H (k:=k) (by unfold k critical; omega) (by omega)|>.some) f hf (by obtain ⟨C,hC⟩:=hc; exact ⟨C,hC.weaker (by simp [price])⟩) ht]
     suffices ∀i:Fin (k+1), (returner D h) (primary R s (some (k-i.val)) (piece B D Y k i.val) f) t=0 by simp only [this]; rw [Finset.sum_const_zero,add_zero]; unfold primary; rw [nested H h hh hk ht]
     intro i
     rw [afterTerm H hd hh hs (a:=(pieceAdmitted H rfl hd' (by omega) i|>.some)) f hf (by
          obtain ⟨C,hC⟩:=hc; refine ⟨C,hC.weaker (by change k-i.val+1≤1+σ; unfold k critical; omega)⟩) ht]
     unfold primary term piece; simp only [miss_center_le H (by exact (Nat.le_of_lt_succ i.isLt).trans hk) hh t ht, smul_zero,integral_zero]
   simp_rw [rule,if_neg hd']
   exact afterTerm H hd hh hs (basicAdmitted H (lt_of_not_ge hd')|>.some) f hf (by obtain ⟨C,hC⟩:=hc; exact ⟨C,hC.weaker (by simp [price])⟩) ht
omit H hd [(volume:Measure E).IsAddHaarMeasure] [BorelSpace E] [MeasureSpace E] in
lemma rate_congr {p:ℝ}{Z Z':ℝ→Target L→(E→ℂ)→ℂ}{n:ℕ}:
     (∀ t∈A, ∀s:ℝ,0<s→∀f:E→ℂ,ContDiff ℝ ∞ f→(∃c,JetBounds n f c)→Z s t f=Z' s t f)→Rate p n A Z'→Rate p n A Z:=by
   intro hh h M hM;obtain ⟨c,hc,hp⟩:=h M hM
   refine ⟨c,hc,fun t ht f hf hw c' hC s r hr hr' rs=>?_⟩
   rw [hh t ht s (hr.trans_le rs) (scaled r f) ((hf.comp (contDiff_const.smul contDiff_id)).const_smul _) (exists_scaled_jetBounds hf hw n hr)]
   exact hp t ht f hf hw c' hC s r hr hr' rs

lemma highPrice {h:ℕ}(hh:h≤Hmax)(hk:critical σ E≤h) :∃γ:ℝ,0<γ∧ Rate ((h:ℝ)-σ+γ) (1+σ) A (fun s t f=>extMiss B D R s σ h Y t f):=by
    obtain ⟨c,γ,hγ,hc⟩:=H.signed h hh; have he':0<γ/2:=by linarith
    let n : ℝ:=Module.finrank ℝ E
    have hg:admissible none ((h:ℝ)-↑σ+γ) (γ/2) n:=by
        change γ/2≤_+γ+_; dsimp only [n]; linarith [show (σ:ℝ)≤h+Module.finrank ℝ E from by exact_mod_cast (by unfold critical at hk; omega : σ≤ h+Module.finrank ℝ E)]
    have he:=termRate hd hc he' hg (j:=1+σ) (by simp [price])
    rw [show (h:ℝ)-σ+γ-(γ/2)=h-σ+γ/2 by ring] at he
    exact ⟨γ/2,he',rate_congr (fun t ht s hs f hf hc=> afterHigh H hd hh hk hs hf hc t ht) he⟩
lemma remainderPrice {h:ℕ}(hh:h≤Hmax)(hk:critical σ E≤Hmax) : ∃γ:ℝ,0<γ∧ Rate ((h:ℝ)-σ+γ) (1+σ) A (fun s t f=>extMiss B D R s σ h Y t f):=by
     by_cases hp : critical σ E≤h
     · exact highPrice H hd hh hp
     set k:=critical σ E; have hK:Module.finrank ℝ E ≤ σ:=by unfold k critical at hp; omega
     let X:=miss D k Y; let a:= (signedAdmitted H (k:=k) (by unfold k critical; omega) hk).some
     let f(i:Fin (k+1)):=piece B D Y k i.val
     have hY(i:Fin (k+1)):∃c ε:ℝ, 0<ε ∧ ε≤1/2 ∧ ∀t∈A,Kas R (↑(i.val)-1-σ+ε) c (miss D h (f i) t):=by
         obtain ⟨c,ε,hε,hε',hw⟩:=piecePrice H B i.val (Nat.le_of_lt_succ i.isLt) hk
         exact ⟨_,ε,hε,hε',missPrice H hh ((centerPrice H (by change i.val≤Hmax; omega) hw).choose_spec.2) |> Exists.choose_spec⟩
     choose c ε hε hw using hY
     have he:∀ᶠ u:ℝ in 𝓝 0,∀i:Fin (k+1),u< ε i/2:= eventually_all.mpr (fun i=>gt_mem_nhds (div_pos (hε i) zero_lt_two))
     obtain ⟨γ,hγ,hγ'⟩:= ((he.filter_mono (nhdsWithin_le_nhds (s:=Ioi 0))).and self_mem_nhdsWithin).exists
     choose c₀ ε' h₀ hc using H.signed k hk; set ξ := min γ (ε'/2)
     have hξ : 0<ξ:=lt_min (by exact hγ') (by linarith)
     refine ⟨ξ,hξ,?_⟩
     let p:=(h:ℝ)-(σ:ℝ)+ξ
     let main (s:ℝ)(t:Target L)(f:E→ℂ):=returner D h (primary R s none X f) t
     have hX' : Rate p (σ+1) A main :=by
         refine rate_congr ?_ ((termRate (m:=none) hd (missPrice H hh hc).choose_spec hξ (by
            unfold admissible; have hq:= congr_arg (fun y:ℕ=>(y:ℝ)) (show k=σ-Module.finrank ℝ E from rfl); rw [Nat.cast_sub hK] at hq; linarith only [hq,min_le_right γ (ε'/2),h₀]) (j:=σ+1) (by simp [price])).weaker (by
              have ht:(h:ℝ) ≤ k:=by exact_mod_cast (show h ≤ k by omega)
              dsimp [p]; have hξ': ξ ≤ ε'/2 := min_le_right ..; linarith only [hξ',ht]) le_rfl)
         intro t ht s hs g hg hW
         exact afterTerm H hd hh hs a g hg (by obtain ⟨c,hc⟩:=hW; exact ⟨c,hc.weaker (by simp [price])⟩) ht
     let U(i:Fin (k+1))(s:ℝ)(t:Target L)(g:E→ℂ) := returner D h (primary R s (some (k-i.val)) (f i) g) t
     have hu (i:Fin (k+1)) : Rate p (σ+1) A (U i):=by
        have hii:=Nat.le_of_lt_succ i.isLt; let b':= (pieceAdmitted (B:=B) H rfl hK hk i).some; let m:= some (k-i.val); have hm:price m≤σ+1:=by change k-i.val+1≤_; unfold k critical; omega
        refine rate_congr (Z':=fun s t g=>primary R s m (miss D h (f i)) g t) ?_ ?_
        · intro t ht s hs g hg hf
          exact afterTerm H hd hh hs b' g hg (by obtain ⟨c,hc⟩:=hf; exact ⟨c,hc.weaker hm⟩) ht
        by_cases hi:i.val≤h
        · exact rate_congr (Z':=0) (fun t ht s hs g hg hf=>by unfold primary term f piece; simp only [miss_center_le H hi hh t ht, smul_zero,integral_zero,Pi.zero_apply]) Rate.zeroR
        have hm':admissible m ((i.val:ℝ)-1-σ+ε i) ξ (Module.finrank ℝ E) :=by
            dsimp only [m,admissible];rw [show ((k-i.val:ℕ):ℝ)=_ from Nat.cast_sub hii]
            have hx: (k:ℝ)=σ-Module.finrank ℝ E:=Nat.cast_sub hK
            have hξ' : ξ ≤ γ:=min_le_left ..
            constructor; all_goals linarith only [hξ',hγ i,(hw i).1, hx,hξ]
        exact (termRate (m:=m) hd (hw i).2 hξ hm' hm).weaker (by
            have hv:(h:ℝ)+1 ≤ i.val:=by exact_mod_cast (show h+1 ≤ i.val by omega)
            have hx: ξ ≤ γ:=min_le_left ..
            dsimp [p]; linarith only [hv,hx,hγ i]) le_rfl
     have hf : (fun s t f=>extMiss B D R s σ h Y t f)=fun s t g=> main s t g + ∑ i:Fin (k+1), U i s t g := funext fun s=> funext fun t=>funext fun g=>by
         unfold extMiss
         rw [show (fun t=> rule B D R s σ Y t g)=primary R s none X g+∑i:Fin (k+1),primary R s (some (k-i.val)) (f i) g from by ext1 t; simp [rule,hK,k,X,f], map_add,map_sum,Pi.add_apply,Finset.sum_apply]
     rw [hf]; exact (Rate.sum hX' (Rate.sumRate Finset.univ fun i _=>hu i)).weaker (le_refl p) (by omega)

/-- Field coordinates of the extension, in the fixed horizon-`h` detector prescription. -/
def readExtended (B:Splitting P)(D:∀ h,Detector S h)(R s:ℝ)(σ h:ℕ)(Y:Target L→E→ℂ)(f:E→ℂ): S.Field h := readAfter D h (fun t=> rule B D R s σ Y t f)

def ReadRate (w n:ℕ)(p:ℝ)(v:ℝ→(E→ℂ)→S.Field w):Prop:= ∀M:ℝ,M>0 → ∃ c:ℝ,0<c ∧ ∀a:ℝ, ∀f:E→ℂ, ContDiff ℝ ∞ f→(∀ x,f x≠0 → ‖x‖ ≤ M)→JetBounds n f a → ∀s r:ℝ, 0<r → r≤1 → r≤s → ‖v s (scaled r f)‖ ≤ c*a*r^p

omit hd in
lemma fromRate (hh:k≤Hmax)(w:ℕ)(T':S.Field k→ₗ[ℂ]S.Field w){p:ℝ}{n:ℕ}{Z:ℝ→Target L→(E→ℂ)→ℂ}(hr:Rate p n A Z): ReadRate w n p (fun s f=>T' (readAfter D k (fun t=>Z s t f))):= by
   intro M hM; obtain ⟨c,hc,h⟩:=hr M hM
   let g:= LinearMap.toContinuousLinearMap (T'.comp (D k).decode)
   refine ⟨1+‖g‖*c,by positivity,fun a f hf hF ha s r h₀ hr hs=>?_⟩
   have hw:=ha.1; let v := a*r^p; have hv : 0≤v:=by dsimp [v]; positivity
   have hy (i: (D k).probes): ‖Z s ⟨S,i.val⟩ (scaled r f)‖ ≤ c*v:= (h _ (H.active k hh i) f hf hF a ha s r h₀ hr hs).trans_eq (by unfold v; ring)
   refine (g.le_opNorm ..).trans ((mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (mul_nonneg hc.le hv)).mpr hy) (norm_nonneg g)).trans ?_)
   dsimp only [v] at *; linarith only [hv]
lemma readZero (hh:k≤Hmax) (hK:critical σ E≤Hmax){ε:ℝ}(hε:0<ε):
   ReadRate 0 (1+σ) (-(σ:ℝ)-ε) (fun s f=>B.part 0 k (readExtended B D R s σ k Y f)):=fromRate H hh 0 (B.part 0 k) (normal hd H hK hε)
omit hd in
theorem readDifference (k h w:ℕ)(hk:k ≤ Hmax)(hw:h < w)(hh:h≤k)(R':Target L→ℂ): B.part w k ((D k).decode (fun e=>returner D h R' ⟨S,e.val⟩))=B.part w k (readAfter D k R'):=by
       have hx(i:(D k).probes):FilteredAt P ⟨S,i⟩:=H.inherit _ (H.active k hk i)
       let a:=readAfter D h R'
       suffices he : B.part w k ((D k).decode (fun e:(D k).probes=> response S h e.val a))=0 by
         change B.part w k ((D k).decode ((fun e:(D k).probes=>R' ⟨S,e.val⟩)-(fun e:(D k).probes=> response S _ (↑e:Exterior L) a)))= _
         rw [map_sub,map_sub,he,sub_zero]; rfl
       rw [show (fun (e:(D k).probes)=> response S h e a)=_ from funext fun e=>(hx e h k hh a).symm,Detector.fixes,B.part_rise H.symmetric H.respects,B.beyondZero hw,LinearMap.zero_apply]

lemma readExtended_diff {k h w:ℕ} (hk:k≤Hmax)(hw : h < w)(hh:h≤k)(s:ℝ)(f:E→ℂ):
       B.part w k (readField D (fun t (_:E)=>extMiss B D R s σ h Y t f) k 0)=B.part w k (readExtended B D R s σ k Y f) := by
       exact readDifference H k h w hk hw hh (fun t=>rule B D R s σ Y t f)
set_option maxHeartbeats 800000 in
lemma readEstimate (hh:k≤Hmax) (hK:critical σ E≤Hmax) (w:ℕ)(hw:w≤k):
   ∃ γ:ℝ,0<γ∧ ReadRate w (1+σ) (w-1-(σ:ℝ)+γ) (fun s f=>B.part w k (readExtended B D R s σ k Y f)):=by
   by_cases he: w=0
   · subst w; refine ⟨1/2,one_half_pos,?_⟩
     rw [show (↑(0:ℕ):ℝ)-1-(σ:ℝ)+1/2=-(σ:ℝ)-1/2 by push_cast; ring]
     exact readZero (B:=B) H hd hh hK one_half_pos
   let h:=w-1; let Z:=fun s t f'=> extMiss B D R s σ h Y t f'
   have hp := fun f s=>readExtended_diff (B:=B) H hd hh (show h<w by omega) (show h≤k by omega) s f
   obtain ⟨γ,hγ,hx⟩:=remainderPrice (B:=B) H hd (le_trans (show h≤w by omega) (hw.trans hh)) hK
   refine ⟨γ,hγ,?_⟩
   have hv := fromRate (D:=D) (p:=((h:ℝ)-σ+γ)) (n:=1+σ) (Z:=fun s t f=>Z s t f) H hh w (B.part w k) hx
   have hw : ((w-1:ℕ):ℝ) = (w:ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ w),Nat.cast_one]
   have hc := funext fun s=> funext (hp · s)
   rw [← hw]
   apply hc ▸ (?_:ReadRate _ _ _ (fun s f=> B.part w k (readField D (fun t (_:E)=> Z s t f) k (0:E))))
   change ReadRate _ _ _ (fun s f=> B.part w k (readField D (fun t (_:E)=> Z s t f) k (0:E))) at hv
   exact hv
end YM.MultipleContact.Power
