import YM.MultipleContact.Bunch.Guard

/-! Finite-dimensional interpolation across joint clusters not tensor tests. Charges only comparable separated configurations here. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.MultipleContact.Bunching
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Acme Ribbons Around Cells Wilson Lattice Climb Set
open Matching
open scoped Topology BigOperators Classical ContDiff
open YM.Next.UVStress Local
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}{W:DiffPlan S} {n':ℕ}[Inhabited (Fin n')]
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i) ∈ conf (n i+1))
variable (hw:Note C.S (fun i=>fuga C.path.levels (i+1)) (-1))
local notation "R'"=>fun (m:ℕ)=> fuga C.path.levels (m+1)
local notation "Yb"=>fun (m:ℕ)=> topZone C.path.levels (C.S.block m) (m+1)
variable (q:∀i:ι,Fin (n i)→ C.book.Token)(lamp:Lattice.Side)

def blend {L:Register G}{n:ι→ℕ}{S:Table L}(q:∀i:ι,Fin (n i)→ L.Token)(V:Fin n'→S.Tag) (c:ι→ℂ)(z:∀i,Points (n i))(y:Fin n'→E4) := ∑ i:ι,c i * many V (q i) y (z i)

def lumps {m:ℕ} (V:Fin n'→S.Tag)(p:Fin m→S.Tag)(m_unused:ℕ:=0) :ℕ:= Clouds (C:=C) (expose ∘ Fin.append V p)
-- ambient differential estimates from Sally.maine
open Line
set_option quotPrecheck false
private lemma birth_step {m:ℕ}(W:DiffPlan S)(V:Fin n'→S.Tag)(p:Fin m→S.Tag)(k:Fin n')(a:Axis)(D:ℕ):
    Clouds (C:=C) (expose ∘ Fin.append (Line.tags V W k a D) p) = Clouds (C:=C) (expose ∘ Fin.append V p)+D:=by
       have hy(i):((expose∘ Line.tags V W k a D) i).fst+2 = ((expose∘ V) i).fst+2 + (if i=k then D else (0:ℕ)):=by
          dsimp only [Function.comp_apply, Line.tags]; by_cases h:i=k
          · simp [h,expose,trek_h,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
          simp [h]
       unfold Clouds; simp only [Fin.sum_univ_add, Function.comp_apply,Fin.append_left,Fin.append_right]
       change (∑ x:Fin n', (((expose ∘ Line.tags V W k a D) x).fst+2)) + _ = _
       simp_rw [hy,Finset.sum_add_distrib]; simp; omega

variable (V:Fin n'→S.Tag)
variable (hc:S.Hierarchy)(hp:F.PointLimits C S)
variable (hq:Cells.CellHyp C F)(hC:C.Makes)
variable {β h τ:ℝ} {cost:ℕ→ℝ} {j:ℕ→ℕ}
variable (hc':Note C.S cost β)(ht:1<τ)(hj:Tendsto j atTop atTop)(hJ:Tendsto (fun m:ℕ=> C.S.scale (j m)/C.S.scale m) atTop (𝓝 τ)) (sign:((i:ι)→Points (n i))→(ι→ℂ)→Prop)
include hK hsafe hw hc hp hq hC hc' ht hj hJ
lemma step_cost (W:DiffPlan S) {u:ι}(k:Fin n')(b:Axis)(D:ℕ)
        (hx:(lumps V (S.classTokens∘q u) 0:ℝ) -h - β < D*(τ-1)):
        ∀ᶠ m in atTop,∀ r> (0:ℝ), r≤ (Yb) m → (R') m ≤r → ∀z∈K,∀y,Cord.Band n' lamp r y →
            ((R') m)^h * ((C.S.a (j m))^D * ‖many (Line.tags V W k b D) (q u) y (z u)‖) ≤ cost m:=by
    let v:=Fin.append (Line.tags V W k b D) (S.classTokens∘q u)
    have hpD:Note C.S (C.S.a∘ j) (-τ):=((Note.note_a C.S).relay j hj hJ).swapP (by ring)
    obtain ⟨l,hl⟩:= exists_nat_gt ((((↑(n u):ℝ)+n')*6))
    have hv': (((Clouds (C:=C) (expose ∘ v):ℕ):ℝ))+D*(-τ)+h*(-1)<β:=by
       rw [show Clouds (expose∘v) (C:=C)=lumps V (S.classTokens∘q u) 0 + D from birth_step W V _ k b D]
       push_cast; linarith only [hx]
    have he:= ((Note.longer (C:=C) (Note.glory (C:=C) v) (1+l)).mills (hpD.powerN D) |>.mills (hw.powr h)).outweigh hc' hv'
    have hm': (n'+n u:ℝ)*6 < l:= by linarith only [hl]
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (Ribbons.maine hC hq hp hc (q:=v) l (by exact_mod_cast hm')),he,Guard.fits (n':=n') K hK hsafe hw lamp] with m hm he hf r hr hy hr' z hZ y hy'
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hm _ (hf r hr' hy z hZ y hy' u)) (pow_pos (C.S.a_pos (j m)) D).le) (Real.rpow_nonneg ((hw.pos _).le) h)).trans (he.trans' (by
       change ((R') m)^h * (C.S.a (j m)^D * honor C.S (expose∘v) (m+1+l)) ≤ (honor C.S (expose∘v) (m+(1+l)) * (C.S.a (j m)^D))*((R') m)^h
       rw [show m+1+l=m+(1+l) by omega]; nlinarith
    ))

variable (hm:W.Derivatives S)
include hm
lemma spread_patch
       (HE:∀ᶠ m in atTop,∀r, (R') m ≤ r → r≤ (Yb) m → ∀ z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1 → sign z c → ∀ y:Fin n'→E4,Cord.Band n' lamp r y → (∀i,Cord.Placed _ (C.S.a (j m)) y i) → ‖((R') m)^h • blend q V c z y‖≤cost m):
       ∃A> (0:ℝ),∀ᶠ m in atTop,∀r:ℝ,(R') m ≤ r → r≤ (Yb) m →∀ z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1→ sign z c→ ∀ y:Fin n'→E4,Cord.Near n' lamp r y → ‖((R') m)^h • blend q V c z y‖≤cost m*A:=by
    let L(i:ι):ℝ:= (lumps V (S.classTokens∘q i) 0:ℝ) -h - β
    have hw':Tendsto (fun k:ℕ=>(k:ℝ)*(τ-1)) atTop atTop:= Tendsto.atTop_mul_const (sub_pos.mpr ht) tendsto_natCast_atTop_atTop
    obtain ⟨D,hD⟩:= (eventually_all.mpr fun i=> hw'.eventually_gt_atTop (L i)).exists
    obtain ⟨A,hA,HH⟩:= Cord.sample lamp D n'
    refine ⟨A,hA,?_⟩
    have hpiece := fun (i:ι)(k:Fin n') b=> step_cost K hK hsafe hw q lamp V hc hp hq hC hc' ht hj hJ W k b D (hD i)
    have hpPos := Cord.radius_pos n' D
    have hx: Note C.S (fun i:ℕ=>Cord.radius n' D*C.S.a (j i)) (-τ):= ((Note.notes C.S _ hpPos).mills ((Note.note_a C.S).relay j hj hJ)).swapP (by ring)
    have hy: Note C.S (fun i:ℕ=> Cord.tolerates n' ((R') i)) (-1):= (hw.splits (Note.notes C.S _ (by positivity))).swapP (sub_zero _)
    have hK':= hx.outweigh hy ?_; swap; · linarith only [ht]
    filter_upwards [HE,eventually_all.mpr fun i=>eventually_all.mpr fun k=>eventually_all.mpr fun b=>hpiece i k b,hK',Guard.fits (n':=n') K hK hsafe hw lamp] with m he hp' hs' hcG r hr hr' z hz c hm' hsign y hY
    apply HH r (C.S.a (j m)) (cost m) (C.S.a_pos _) (hc'.pos _) ((hw.pos m).trans_le hr) (hs'.trans (by apply div_le_div_of_nonneg_right hr; positivity)) _ (he r hr hr' z hz c hm' hsign) ?_ y hY
    intro ⟨k,b⟩ hk x hband
    let a':= C.S.a (j m); let r0:= ((R') m)^h
    let f(i:ι) (p:ℕ)(t:ℝ):= (a'^p:ℝ) • many (Line.tags V W k b p) (q i) (Cord.polar (k,b) x a' t) (z i)
    refine ⟨fun p t=>∑ i,r0 • (c i * f i p t),?_,?_,fun t ht=>?_⟩
    · funext t; unfold f blend; simp only [Function.comp_apply, Finset.smul_sum]
      simp only [a',r0,pow_zero,one_smul, Line.tags,trek,update_eq_self]
    · intro j hj' t ht'; exact HasDerivAt.fun_sum (fun i _=> ((Line.deriv V q W hc hm x a' k b z i t (slide_conf C.S _ (hcG r hr hr' z hz _ (hband _ ht') i)) j).const_mul (c i)).const_smul r0)
    calc _ ≤ ∑ i:ι, (‖c i‖*cost m) := (norm_sum_le ..).trans <| Finset.sum_le_sum fun i _=> by
                 change ‖r0 • (c i*f i D t)‖≤ _
                 unfold f; rw [norm_smul,norm_mul,norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg ((hw.pos m).le) h), Real.norm_of_nonneg (pow_nonneg (C.S.a_pos (j m)).le D),mul_left_comm]
                 exact mul_le_mul_of_nonneg_left (hp' i k b r ((hw.pos m).trans_le hr) hr' hr z hz _ (hband _ ht)) (norm_nonneg (c i))
         _ ≤ cost m:=by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left (hc'.pos m).le hm'
end YM.MultipleContact.Bunching
