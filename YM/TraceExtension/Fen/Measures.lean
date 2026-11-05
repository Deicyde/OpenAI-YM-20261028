import YM.TraceExtension.Fen.Black
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {d k:ℕ}{σ A C:ℝ}(R:Rep G n) (h:R.path.Bounds R.clip σ A C)
include h
lemma off_budget : SumBudget (fun i=> port R (legF i) * Real.exp (σ*mote R (legF i))) (Geo.lowerSize R.clip A+(A+A)):= Cost.sum (Geo.lower_budget G R.path h) (Cost.sum h.three h.four)
lemma offloop : SumBudget (fun i=>port R (loopF i) * Real.exp (σ*mote R (loopF i))) C:= h.two
lemma offull : SumBudget (fun i=> port R i*Real.exp (σ*mote R i)) (Geo.lowerSize R.clip A+((A+A)+C)):= Cost.sum (Geo.lower_budget G R.path h) (Cost.sum (Cost.sum h.three h.four) h.two)
section
omit h
lemma occidental (x:Seat n)(j:Barley): x.2∈officeC R x j:= (Seat.reg x (fort R j) (sloop R _)).anchor
lemma post_geo(s:Seat n)(i: Barley): R.p.B*coverNumber R.p.B (officeC R s i) ≤ R.p.B*100 + mote R i:=by
    rw [offt]; cases i with
    | inl j=> exact le_trans (Geo.low_geometry R.p R.path j (0:Site n)) (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by decide)) _)
    | inr j=>
       have h:= Next.Scheduling.Wages.traversed (tooth R j) (0:Site n) R.p.B R.p.B_pos; change R.p.B * coverNumber R.p.B ((tooth R j).footprint 0) ≤ _ + (tooth R j).length; have hk:rowD j≤4:=by cases j with
            | inl k=> cases k <;> norm_num[rowD,High.arity]
            | inr k=> exact le_refl 2 |>.trans (by decide : 2 ≤ 4)
       apply h.trans; nlinarith
lemma boundL (s:Seat n)(i:Barley): officeC R s i⊆ sprout s.2 ((coverNumber R.p.B (officeC R s i))*(4*R.p.B+2)+2*R.p.B):=by
   intro y hy; apply halo_spec.mpr; refine ⟨_,mem_singleton_self s.2,?_⟩; have hv:= Corona.extent _ R.p.B (occidental R s i) hy; exact hv
lemma boundsGeo (s:Seat n)(i:Barley):officeC R s i ⊆ sprout s.2 (900*(R.p.B+mote R i)):=by
    apply (boundL R s i).trans; apply sprout_mono; have he:=post_geo R s i; have hz:= R.p.B_pos; have hP:= Nat.mul_le_mul_right (coverNumber R.p.B (officeC R s i)) (show 1 ≤ R.p.B from hz); simp only [one_mul] at hP
    nlinarith only [he,hP,show 0≤ mote R i from Nat.zero_le _]
lemma surrounds (s:Seat n)(i:Barley)(x:Site n)(h:x∈officeC R s i): officeC R s i⊆ sprout x (1800*(R.p.B+mote R i)):=by
    let M:=900*(R.p.B+mote R i); have hz:=boundsGeo R s i; apply hz.trans; have he : separation x s.2≤ M:= by rw [separation_comm]; simpa only [Turret.sprout,halo_spec,mem_singleton,exists_eq_left] using (hz h)
    rw [show 1800*(R.p.B+mote R i)= M+M by unfold M; ring]; exact hedge he M
lemma precinct (x:Site n)(i:Barley): (univ.filter fun s:Seat n=> x∈officeC R s i).card ≤ Fintype.card Signed * ((2*900*(R.p.B+mote R i)+1)^4):=by
    let Q:= sprout x (900*(R.p.B+mote R i)); let P:= univ (α:=Signed) ×ˢ Q
    refine (card_le_card (t:=P) (fun s hs=> mem_product.mpr ⟨mem_univ _,?_⟩)).trans ?_
    · have ht:=boundsGeo R s i ((mem_filter.mp hs).2); obtain ⟨v,hv,h⟩:=halo_spec.mp ht; exact halo_spec.mpr ⟨x,mem_singleton_self _,by rw [separation_comm, ← mem_singleton.mp hv]; exact h⟩
    unfold P Q; rw[card_product,card_univ]; gcongr; apply (Corona.halo_size ..).trans; rw [card_singleton,one_mul]; gcongr; omega
-- arrival cost for near site, no Sig outside Hull. cheap power
def bankCost(B:ℕ):ℝ:= Fintype.card Signed * (2000*(B+1:ℕ):ℕ)^ (4:ℕ)
lemma swag (x:Site n)(i:Barley): (↑(univ.filter fun s:Seat n=>x∈officeC R s i).card:ℝ) ≤ bankCost R.p.B*(1+mote R i)^4:=by
    let p:= R.p.B; let t:= mote R i
    have hx:2*900*(p+t)+1≤ 2000*(p+1)*(1+t):=by nlinarith
    have ht:= le_trans (precinct R x i) (Nat.mul_le_mul_left _ (pow_le_pow_left' hx _))
    refine le_trans (Nat.cast_le.mpr ht) (le_of_eq ?_); unfold bankCost; unfold p t;push_cast;ring
end
end YM.Trace.Fen
