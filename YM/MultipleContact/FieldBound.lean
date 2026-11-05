import YM.MultipleContact.Detector
import YM.MultipleContact.Direct
import Mathlib.MeasureTheory.SpecificCodomains.Pi

set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Power
open Function Filter MeasureTheory Set TopologicalSpace Metric Table Direct Analysis Extraction
open scoped Topology BigOperators ContDiff Classical
variable {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E]
 [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure]
variable {G : Gauge}{L:Register G}{S T:Table L}{P:DiffPlan S}

abbrev Target (L:Register G):= Table L × Exterior L
variable (D:∀ h,Detector S h)
variable {Y Z : Target L→E→ℂ} {R:ℝ} {σ Hmax h k:ℕ} {A:Set (Target L)}

def readField (Y : Target L→E→ℂ) (h:ℕ) (y:E): S.Field h:= (D h).decode (fun e:(D h).probes=>Y ⟨S,(e:Exterior L)⟩ y)
def centerRead (h:ℕ) (v:E→ S.Field h): Target L→ E→ℂ:=fun t y=>response t.1 _ t.2 (v y)
def miss (h:ℕ) (Y : Target L→E→ℂ): Target L→ E→ℂ := Y - centerRead h (readField D Y h)

def FilteredAt (P:DiffPlan S) (t: Target L):Prop:=∀ h k, ∀ he:h≤k,∀ x:S.Field h,response t.1 k t.2 (P.rise he x)=response t.1 h t.2 x
lemma response_use (t:Target L) (h:t.1.Symmetric)(he:t.1.respects S) (k:ℕ)(v:S.Field k):
  response t.1 k t.2 v= S.useAt t.1 t.2.point (Fin.cons ⟨k,v⟩ (S.classTokens∘t.2.letter)):=by
    let w:= Fin.cons (α:=fun _=> S.Tag) ⟨k,v⟩ (S.classTokens∘t.2.letter)
    let q:= Fin.cons (α:=fun _=> L.Token) ⟨k,S.representative _ v⟩ t.2.letter
    have hh:w=S.classTokens∘q:=funext fun i=> Fin.cases (by
      simp only [w,q,Fin.cons_zero,comp_apply]; change (⟨k,v⟩:S.Tag)= ⟨k,S.project k (_)⟩; rw [S.rep]) (fun j=> by simp [w,q]) i
    change _=S.useAt t.1 _ w; rw [hh,S.at_project t.1 h he t.2.clear]
    rfl
lemma filtered (t:Target L)(h:t.1.Symmetric)(he:t.1.respects S) (hr:P.Inclusions t.1) : FilteredAt P t:= fun k e he' x=>by
     simpa only [response_use t h he] using hr.kernels he' x t.2.clear (S.classTokens∘t.2.letter)

structure Estimates (P:DiffPlan S) (D:∀ h,Detector S h)(σ Hmax:ℕ)(R:ℝ)(Y:Target L→E→ℂ) (A:Set (Target L)): Prop where
  radius_pos : 0<R
  radius_le : R≤1
  symmetric : S.Symmetric
  respects : P.Inclusions S
  inherit (t) : t∈A → FilteredAt P t
  active k : k≤ Hmax → ∀ e:(D k).probes, ⟨S,e.val⟩∈A
  output k : k≤Hmax→∃ c:ℝ, 0<c ∧ ∀t∈A,∀v:S.Field k,‖response t.1 k t.2 v‖≤ c*‖v‖
  grow (ε:ℝ): 0<ε → ∃ c:ℝ, ∀ t∈A, Kas R (-(σ:ℝ)-ε) c (Y t)
  signed k: k≤ Hmax → ∃ c γ:ℝ, 0<γ ∧ ∀ t∈A, Kas R ((k:ℝ)-σ+γ) c (miss D k Y t)

local notation "ρ" => volume.restrict (ball 0 R)
variable {D}
omit [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma read_kas (_hk:k≤Hmax)(hA:∀ e:(D k).probes, ⟨S,e.val⟩∈A){Z : Target L→E→ℂ} {p c:ℝ} (hv:∀t∈A, Kas R p c (Z t)):
    ∃ c',Kas R p c' (readField D Z k):=by
      let r := readField D Z k
      let F:= LinearMap.toContinuousLinearMap (D k).decode
      have he y: r y = F fun e=> Z (S,(e:Exterior L)) y := rfl
      have h' (e:(D k).probes) : Kas R p c (Z ⟨S,e⟩):=hv _ (hA e)
      have ha : AEStronglyMeasurable r (volume.restrict (ball 0 R)):=by
          simp_rw [show r=_ from funext he]
          exact F.continuous.comp_aestronglyMeasurable ((aemeasurable_pi_iff.mpr fun e=>(h' e).measurable.aemeasurable).aestronglyMeasurable)
      let t:= max 1 c; have ht : 0<t := lt_of_lt_of_le zero_lt_one (le_max_left ..)
      refine ⟨‖F‖*t+1,by positivity,ha,fun x hx hW=>?_⟩
      change ‖r x‖ ≤ _; rw [he]
      have hp : 0 ≤ t*‖x‖^p := by positivity
      apply le_trans (F.le_opNorm ..)
      calc _ ≤ ‖F‖*(t*‖x‖^p) := mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hp).mpr (fun e=>(h' e).grow x hx hW |>.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)))) (show 0≤‖F‖ from by positivity)
           _ ≤ _ := by nlinarith [Real.rpow_nonneg (norm_nonneg x) p]

section Algebra
variable (H:Estimates P D σ Hmax R Y A)
include H

omit [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma miss_read (hh:h≤k)(hK:k≤Hmax)(y:E):readField D (miss D h Y) k y=readField D Y k y-P.rise hh (readField D Y h y):=by
      have he(e:(D k).probes):response S k e (P.rise hh (readField D Y h y))=response S h e (readField D Y h y) := H.inherit _ (H.active _ hK _) h k hh _
      change (D k).decode ((fun e:(D k).probes=>Y ⟨S,e⟩ y)-(fun e:(D k).probes=>response S h e (readField D Y h y)))=_
      simp_rw [map_sub,← he,Detector.fixes]; rfl

omit [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma piece_miss (B:Splitting P)(w:ℕ)(hw:w≤k)(hK:k≤Hmax)(hh:0<w) (y:E): B.part w k (readField D Y k y)= B.part w k (readField D (miss D (w-1) Y) k y):=by
     rw [miss_read H (by omega) hK,map_sub,B.part_rise H.symmetric H.respects,B.beyondZero (by omega : w-1 < w),LinearMap.zero_apply,sub_zero]

omit [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] H in
lemma lower_kas {F:Type*}[NormedAddCommGroup F]{R:ℝ} (hR:R≤1){p p' c:ℝ}(hp:p≤p') {K:E→F}(hv:Kas R p' c K): Kas R p c K:=by
    refine ⟨hv.pos,hv.measurable,fun x hx hW=> (hv.grow x hx hW).trans ?_⟩
    have hx:=Metric.mem_ball.mp hx; rw [dist_zero_right] at hx; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hW) (hx.le.trans hR) hp) hv.pos.le


lemma piecePrice (B:Splitting P)(w:ℕ)(hw:w≤k)(hK:k≤Hmax):∃ c γ:ℝ,0<γ ∧ γ≤1/2 ∧ Kas R ((w:ℝ)-1-σ+γ) c (fun y=> B.part w k (readField D Y k y)) := by
     let v := B.part w k; let F:= LinearMap.toContinuousLinearMap v
     suffices h:∃c γ:ℝ,0<γ∧γ≤1/2∧∃g:E→S.Field k,Kas R ((w:ℝ)-1-σ+γ) c g ∧ ∀ y:E,F (g y)= v (readField D Y k y) by
        obtain ⟨c,gamma,hg,hg',g,Hg,hg''⟩:=h
        have hh:= Hg.pos
        refine ⟨‖F‖*c+1,gamma,hg,hg',?_,?_,?_⟩
        · positivity
        · change AEStronglyMeasurable (fun y=>v (readField _ _ _ _)) (volume.restrict _); simp only [← hg'' ]; exact F.continuous.comp_aestronglyMeasurable Hg.measurable
        intro x hx hW; set p:=((w:ℝ)-1-σ+gamma)
        change ‖v (_)‖ ≤ _; rw [← hg'']
        exact (F.le_opNorm ..).trans ((mul_le_mul_of_nonneg_left (Hg.grow x hx hW) (norm_nonneg F)).trans (by nlinarith [Real.rpow_nonneg (norm_nonneg x) p]))
     by_cases hz:w=0
     · obtain ⟨c,hc⟩:=H.grow (1/2) one_half_pos
       obtain ⟨C,hC⟩:=read_kas hK (H.active k hK) hc
       exact ⟨C,(1/2),one_half_pos,le_rfl,_,by convert hC using 1; rw [hz]; push_cast; ring,fun y=>rfl⟩
     have hh:w-1≤Hmax:=by omega
     obtain ⟨c,γ,hγ,hc⟩:=H.signed (w-1) hh
     obtain ⟨C,hC⟩:=read_kas hK (H.active k hK) hc
     refine ⟨C,min γ (1/2),lt_min hγ one_half_pos,min_le_right ..,_,lower_kas H.radius_le (?_) hC,fun y=>(piece_miss H B w hw hK (by omega) y).symm⟩
     rw [Nat.cast_sub (by omega : 1≤w)]; linarith only [min_le_left γ (1/2), Nat.cast_one (R:=ℝ)]
lemma centerPrice {v:E→S.Field k}{p c:ℝ}(hk:k≤Hmax)(hv:Kas R p c v):∃c'>0,∀ t∈A,Kas R p c' (centerRead k v t):=by
   obtain ⟨t,ht,hq⟩:= H.output k hk
   refine ⟨t*c,mul_pos ht hv.pos,fun x hx=>⟨mul_pos ht hv.pos, ?_,fun y hy hz=> ?_⟩⟩
   · exact (response (S:=S) x.1 k x.2).continuous_of_finiteDimensional.comp_aestronglyMeasurable hv.measurable
   exact (hq _ hx _).trans ((mul_le_mul_of_nonneg_left (hv.grow y hy hz) ht.le).trans_eq ((mul_assoc ..).symm))

omit [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] H in
lemma subPrice {F:Type*}[NormedAddCommGroup F] {V W:Target L→E→F}{p c b:ℝ}(hv:∀t∈A,Kas R p c (V t))(hW:∀t∈A,Kas R p b (W t)): ∀t∈A, Kas R p (c+b) (V t-W t):=by
  intro t ht;let hx:=hv t ht;let hy:=hW t ht
  refine ⟨add_pos hx.pos hy.pos,hx.measurable.sub hy.measurable,fun y h h'=>?_⟩
  rw [add_mul]; exact (norm_sub_le ..).trans (add_le_add (hx.grow y h h') (hy.grow y h h'))
lemma readPrice (h:k≤Hmax){Z : Target L→E→ℂ}{p c:ℝ}(hz:∀t∈A,Kas R p c (Z t)):
     ∃c',Kas R p c' (readField D Z k):=read_kas h (H.active k h) hz
lemma missPrice (h':h≤Hmax){Z : Target L→E→ℂ}{p c:ℝ}(hz:∀t∈A,Kas R p c (Z t)): ∃c',∀t∈A,Kas R p c' (miss D h Z t):=by
  obtain ⟨b,_,hb⟩:= centerPrice H h' ((readPrice H h' hz).choose_spec)
  exact ⟨c+b,subPrice (A:=A) hz hb⟩
end Algebra
end YM.MultipleContact.Power
