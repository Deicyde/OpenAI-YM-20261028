import YM.MultipleContact.Bunch.Fill
import YM.MultipleContact.Bunch.Summit
import YM.MultipleContact.Matching.Estimates

/-! Comparable physical-cluster multiple insertions. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.MultipleContact.Bunching
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Acme Ribbons Around Cells Wilson Lattice Climb Set
open scoped Topology BigOperators Classical ContDiff
open YM.Next.UVStress Local Matching
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}{n':ℕ}[Inhabited (Fin n')]
variable {ι:Type*}[Fintype ι]{n:ι →ℕ}
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i)∈conf (n i+1))
variable (q:∀i:ι,Fin (n i)→ C.book.Token)(V:Fin n'→S.Tag)(lamp:Lattice.Side)
variable (H:S.Hierarchy)(hp:F.PointLimits C S)(hq:Cells.CellHyp C F)(hC:C.Makes){W:DiffPlan S}(hm:W.Derivatives S)
variable (hT:Acme.Aroma C)
local notation "R'"=>fun (m:ℕ)=> fuga C.path.levels (m+1)
local notation "Yb"=>fun (m:ℕ)=> topZone C.path.levels (C.S.block m) (m+1)
set_option quotPrecheck false
variable {β h s:ℝ} {cost:ℕ→ℝ} {j:ℕ→ℕ}
variable (hc':Note C.S cost β)(hs:1<s)(hj:Tendsto j atTop atTop)(hJ:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 s)) (sign:((i:ι)→Points (n i))→(ι→ℂ)→Prop)

def Puff (P:((i:ι)→Points (n i))→(ι→ℂ)→Prop)(a:ℝ):Prop:=∃r₀> (0:ℝ), ∀z∈K,∀c:ι→ℂ,(∑i:ι,‖c i‖)≤1→ P z c→ ∀r:ℝ,0<r → r < r₀→∀y:Fin n'→E4,Cord.Near n' lamp r y→ ‖blend q V c z y‖ ≤ r^a

def massOf {G:Gauge}{L:Register G}{S:Table L}(V:Fin n'→S.Tag):ℕ:= totalDeg (fun i=> (V i).1)
include hK hsafe H hp hq hC hm hT hc' hs hj hJ
lemma shell_many (hG:G.Simple)(HE:∀ᶠ m in atTop,∀r:ℝ, (R') m ≤ r → r≤ (Yb) m → ∀ z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1 → sign z c → ∀ y:Fin n'→E4,Cord.Band n' lamp r y → (∀i,Cord.Placed _ (C.S.a (j m)) y i) → ‖((R') m)^h • blend q V c z y‖≤cost m)(γ:ℝ)(hγ:β< -γ):Puff K q V lamp sign (-h+γ):=by
     have hw:= hT.notes
     obtain ⟨A,hA,he⟩:= spread_patch K hK hsafe hw q lamp V H hp hq hC hc' hs hj hJ sign hm HE
     let p := -h+γ
     have hp':Note C.S (fun m=> cost m*A/((R') m)^h) (h+β):= ((hc'.mills (Note.notes C.S A hA)).splits (hw.powr h)).swapP (by ring)
     obtain ⟨M,hM⟩:=eventually_atTop.mp (he.and (hp'.outweigh (hw.powr p) (by dsimp [p]; linarith only [hγ])|>.and (hp'.outweigh ((topNote hw).powr p) (by dsimp [p]; linarith only [hγ]))))
     let r₀:=(R') M
     refine ⟨r₀,hw.pos _,fun z hz c hc' hsign r hr hy y hw0 =>?_⟩

     have hex':∃ n:ℕ, fuga C.path.levels (n+M+1) ≤ r:= by
         have hh:=((hw.thins (show -(1:ℝ)<0 by norm_num)).comp (tendsto_add_atTop_nat M)).eventually (ge_mem_nhds hr)
         exact hh.exists
     let m':=Nat.find hex'; let m:=m'+M
     have hL: (R') m ≤ r:=Nat.find_spec hex'
     have hp₀:m' < m'+1:= by omega
     have hfa:r < fuga C.path.levels (M+1):=hy
     have h0 : 0 < m' := by apply Nat.pos_iff_ne_zero.mpr; intro e; have h:= Nat.find_spec hex'; change fuga C.path.levels (m'+M+1) ≤ _ at h; rw [e,zero_add] at h; exact hfa.not_ge h
     have hfirst : r ≤ fuga C.path.levels m:=by
       apply le_of_not_ge; intro he; have ht:=Nat.find_min hex' (show m'-1 < m' from by omega); exact ht (by rw [show m'-1+M+1=m by dsimp [m]; omega];exact he)
     have hr'' : r≤(Yb) m:=hfirst.trans (radii C hG m) -- hG required!
     obtain ⟨hh,hu,hw'⟩:=hM m (Nat.le_add_left ..)
     have hpos:=Real.rpow_pos_of_pos (hw.pos m) h
     have hT:= hh r hL hr'' z hz c hc' hsign y hw0
     rw [norm_smul,Real.norm_of_nonneg (by exact hpos.le)] at hT
     apply ((le_div_iff₀ hpos).2 ((mul_comm ..).le.trans hT)).trans
     change cost m*A/_ ≤ _
     rcases le_total 0 p with h|h
     · exact hu.trans (Real.rpow_le_rpow (hw.pos m|>.le) hL h)
     exact hw'.trans (Real.rpow_le_rpow_of_nonpos hr hr'' h)

variable (htreas:Treasury C) {r:ℝ}{k:ℕ}
variable (ℓ:∀i:ι,Fin (n i)→ Cover)(hL: ∀i,Injective (Fin.cons (α:=fun _=>Cover) 0 (ℓ i)))
    (hK':∀z∈K,∀ i,Locations C k r (ℓ i) (z i))(hr:0<r)
omit hK hsafe H hp hq hC hm hT hc' hs hj hJ in
private lemma difference_grid (m:ℕ)(x y: Cover) : C.S.gridPoint m (x-y)=C.S.gridPoint m x-C.S.gridPoint m y:=by
    ext i; simp [Schedule.gridPoint]; push_cast; ring
omit hc' hs hj hJ
include htreas hL hK' hr
lemma pack (D:ℕ)(w:ℝ)(hw:0<w):∃ (A s β:ℝ)(j:ℕ→ℕ)(p:ℕ)(E:ℕ→ℝ), 1<s∧0<β∧Note C.S E β∧0<A∧β<w ∧ Tendsto j atTop atTop∧ Tendsto (fun m:ℕ=> C.S.scale (j m)/C.S.scale m) atTop (𝓝 s)∧ ∀ᶠ m in atTop,∀ r:ℝ, (R') m≤ r → r≤Yb m→ ∀ z∈K, ∀ y:Fin n'→E4,Cord.Band n' lamp r y→ (∀i,Cord.Placed _ (C.S.a (j m)) y i) → ∃v:S.Field D,bondedMany q V y ((R') m ^ (massOf V-(D:ℝ))) D z v (outputCost C S m k p D A (E m)) (error C m k p A):=by
    let p0:= (Stock.Tabs.mayOpen C.path.levels 1 hT.opens k).choose; let p:= max p0 (C.ref D)
    let d(i:Fin n'):= (V i).1
    let qV(i):=S.representative (d i) (V i).2
    obtain ⟨w',hw'⟩:=Finite.bddAbove_range (fun i:Fin n'=> (C.labels.level (d i)).coeffSize (qV i))
    obtain ⟨s,j,hs⟩:=htreas.fees' (Fin n') d lamp D k p (w/2) (half_pos hw) (Stock.Tabs.open_later _ _ hT.opens ((Stock.Tabs.mayOpen C.path.levels 1 hT.opens k).choose_spec) (le_max_left ..) zero_le_one) (le_max_right ..) (1+|w'|) (show (0:ℝ)<1+|w'| from add_pos_of_pos_of_nonneg one_pos (abs_nonneg _))
    obtain ⟨-,ht,hβ,hβ',hγ,hj,hJ,M,hM,hf⟩:=hs
    let h:ℝ:=totalDeg d-(D:ℝ)
    obtain ⟨A,hA,hQ⟩:=comparableMany q ℓ H hp hq hC hL hr d (lamp:=lamp) (J:=k)
    have hV: V=(fun i:Fin n'=> (⟨d i,S.project _ (qV i)⟩:S.Tag)):=funext (fun i=> (congr_arg (fun x:S.Field (d i)=>Sigma.mk (d i) x) (S.rep ..)).symm)
    let β:= -((totalDeg d:ℝ)+4*Fintype.card (Fin n'))*(1-s)
    refine ⟨A,s,β,j,p,M,ht,hβ,hM.swapP (by ring),hA,by change β≤w/2 at hγ; linarith,hj,hJ,?_⟩
    filter_upwards [hf qV (fun i=>(hw' (Set.mem_range_self i)).trans (by linarith only [le_abs_self w'])) F,Guard.fits (n':=n') K hK hsafe hT.notes lamp] with m hctr hScl r hr₁ hr₂ z hz y hy htp
    obtain ⟨c,eq,hc,hN⟩:= Guard.onGrid (C:=C) K hK hsafe hT.notes hy.1 htp
    change ∃ v:S.Field D, bondedMany q V y (((R') m)^h) D z v _ _
    rw [eq] at hN hy ⊢
    apply (hV ▸ hQ qV _ _ _ _ _ _ hctr c hc (fun i j h'=> (?_) ) (fun i=>?_) z (hK' _ hz) (fun i=>slide_conf C.S _ (hScl r hr₁ hr₂ z hz _ hy i)) hN)
    · rw [difference_grid]; exact ((hy.2.1 i j h').le.trans' (by linarith only [hr₁]))
    exact (hy.2.2 i).le.trans (by rw [topZone,show (lamp*C.S.block m).val=lamp.val*(C.S.block m).val from rfl,Nat.cast_mul]; change 4*lamp.val*r≤4*((lamp.val*(C.S.block m).val)*(fuga _ _)); have :=Nat.cast_nonneg (α:=ℝ) lamp.val; change r≤(C.S.block m).val*(fuga _ _) at hr₂;nlinarith only [mul_le_mul_of_nonneg_left hr₂ this])
set_option linter.unusedVariables false
variable (hG:G.Simple)
include hG
lemma erased (D:ℕ):Puff K q V lamp (silent q S D) (-(massOf V:ℝ)+D+1/64):=by
    obtain ⟨A,s,β,j,k',E,hs,hβ,hE,hA,_,hj,hJ,HV⟩:=pack K hK hsafe q V lamp H hp hq hC hm hT htreas ℓ hL hK' hr D 1 one_pos
    refine Eq.mp ?_ (shell_many (h:=(massOf V:ℝ)-D) K hK hsafe q V lamp H hp hq hC hm hT (errorNote C k k' A hA) hs hj hJ (silent q S D) (G:=G) ?_ ?_ (1/64) (by norm_num)) -- missing hG unused? supply
    · apply congr_arg (Puff K q V lamp (silent q S D)); ring
    · exact ‹G.Simple›
    filter_upwards [HV] with m hv r hr hr' z hz c hc hcancel y hy ht
    obtain ⟨v,h₀,hv⟩:= hv r hr hr' z hz y hy ht
    have he:(R') m≤r:=hr
    let w:=(R') m ^ ((massOf V:ℝ)-D)
    change ‖w • (∑ i:ι, c i *many V (q i) y (z i))‖ ≤ error _ _ _ _ _
    rw [Finset.smul_sum]; change ‖∑ i,↑w * (c i*many V (q i) y (z i))‖ ≤ _

    have h':(∑ i:ι,↑w*(c i * many V (q i) y (z i)))=∑ i,c i*(↑w*many V (q i) y (z i)-once (q i) (⟨D,v⟩:S.Tag) (z i)):=by simp_rw [mul_sub,Finset.sum_sub_distrib,(show (∑ i,c i*once (q i) ⟨D,v⟩ (z i))=0 from hcancel v),sub_zero]; exact Finset.sum_congr rfl (fun i _=>by ring)
    rw [h']; let p:=error C m k k' A; have hp:0 < p:= errorNote C k k' A hA|>.pos m
    apply (norm_sum_le ..).trans ?_
    calc _ ≤ ∑ i:ι,‖c i‖*p:= Finset.sum_le_sum fun i _=> by rw [norm_mul];exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
         _ ≤ p:=by rw [← Finset.sum_mul];exact mul_le_of_le_one_left hp.le hc

lemma ordinary (ε:ℝ)(hε:0<ε):Puff K q V lamp (fun _ _=>True) (-(massOf V:ℝ)-ε):=by
     obtain ⟨A,s,β,j,k',E,hs,hβ,hE,hA,hβ',hj,hJ',HV⟩:=pack K hK hsafe q V lamp H hp hq hC hm hT htreas ℓ hL hK' hr 0 ε hε

     let f (i:ι)(z:Points (n i)):= Work.A01.frontRead (S.classTokens∘q i) (Points.cons 0 z) 0
     have h0(i z v):once (q i) (⟨0,v⟩:S.Tag) z=f i z v:=(Work.A01.front_eval ..).symm
     obtain ⟨C₀,hC₀,hQ⟩:= normProd_bound K hK hsafe f fun i z hZ v=>by simpa only [← h0] using! once_tends (q i) _ hZ v H
     let cost m:= E m + C₀*((‖LinearMap.toContinuousLinearMap (S.project 0)‖+1)*(lista C 0 m*(2*E m)))
     have hc0: Note C.S cost β := by
           have ht: Note C.S (lista C 0) 0 :=by unfold lista; simp only [pow_zero,mul_one]; exact (futon C).scales C.path.levels.fits.mesh
           apply hE.extra ((((Note.notes C.S C₀ hC₀).mills ((Note.notes C.S (‖LinearMap.toContinuousLinearMap (S.project 0)‖+1) (by have h := norm_nonneg (LinearMap.toContinuousLinearMap (S.project 0)); positivity)).mills (ht.mills ((Note.notes C.S (2:ℝ) zero_lt_two).mills hE)))).swapP (by ring)))
     refine Eq.mp ?_ (shell_many (h:=(massOf V:ℝ)) K hK hsafe q V lamp H hp hq hC hm hT hc0 hs hj hJ' (fun _ _=>True) hG ?_ (-ε) (by linarith only [hβ']))
     · apply congr_arg (Puff K q V lamp (fun _ _=>True)); ring
     filter_upwards [(errorNote C k k' A hA).outweigh hE (by linarith),HV] with m he h r hr hr' z hz c hc' _ y hy htp
     obtain ⟨v,hv,h1⟩:= h r hr hr' z hz y hy htp
     have hL := hc0.pos m
     have ha(i): ‖((R') m) ^ (massOf V:ℝ) • many V (q i) y (z i)‖ ≤ cost m:= by
          set w := ((R') m)^(massOf V:ℝ)
          have he₁:= (h1 i).trans he
          simp only [Nat.cast_zero,sub_zero] at he₁
          calc _ ≤ ‖w • many V (q i) y (z i) - once (q i) ⟨0,v⟩ (z i)‖+‖once (q i) ⟨0,v⟩ (z i)‖ :=by rw [norm_sub_rev _ (once _ _ _), add_comm]; exact norm_le_insert (once _ _ _) _
               _ ≤ _:= add_le_add he₁ ((by
                    rw [h0]; refine (hQ z hz i v).trans (mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_right (show ‖LinearMap.toContinuousLinearMap (S.project 0)‖ ≤ ‖LinearMap.toContinuousLinearMap (S.project 0)‖+1 from by linarith only) (by have he:=hc0.pos m; have he':=Finset.prod_nonneg (s:=Finset.range (m+1)) (f:=fun i=> (C.path.levels.params (i+1)).columns * (↑((C.S.block i).val))^0) (fun k _=>mul_nonneg (zero_le_one.trans (C.path.levels.params (k+1)).columns_ge) (by positivity : 0≤ ((C.S.block k).val :ℝ)^0)); exact mul_nonneg he' (mul_nonneg zero_le_two (hE.pos m).le)))) hC₀.le)))
               _ ≤ cost m := le_refl _
     unfold blend; rw [Finset.smul_sum]; apply (norm_sum_le ..).trans
     calc _ ≤ ∑ i:ι,‖c i‖*cost m:=Finset.sum_le_sum fun i _=>by change ‖↑((R') m^(massOf V:ℝ))*(c i*_)‖≤_; rw [mul_left_comm,norm_mul]; exact mul_le_mul_of_nonneg_left (ha i) (norm_nonneg _)
          _ ≤ cost m :=by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left hL.le hc'
end YM.MultipleContact.Bunching