import YM.MultipleContact.Matching.Continuum
import YM.MergeProof.West.Puppy
import YM.MergeProof.West.Fur
/-! Comparable annulus interpolation with compact uniform constants. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Local
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Climb Set
open Matching
open scoped Topology BigOperators Classical ContDiff
open YM.Next.UVStress
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}{W:DiffPlan S} {t d D J:ℕ}
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i) ∈ conf (n i+1))
include hK hsafe
lemma gapK : ∃δ:ℝ,0<δ∧∀z∈K, ∀i,∀ j k:Fin (n i +1), j≠k→δ< ‖Points.cons 0 (z i) j-Points.cons 0 (z i) k‖:=by
   let f(i:ι)(j k:Fin (n i+1))(z:((i:ι)→Points (n i))):=‖Points.cons 0 (z i) j-Points.cons 0 (z i) k‖
   have he(i:ι) (j k:Fin (n i+1)):∀ᶠ δ in 𝓝 (0:ℝ), j≠k→∀z∈K,δ<f i j k z:=by
     by_cases h:j=k
     · simp_all
     by_cases he : K.Nonempty
     · have hf(w): Continuous (fun z:((i:ι)→Points (n i))=> Points.cons 0 (z i) w):=by fun_prop -- may fail
       obtain ⟨x,hx,hmin⟩:=hK.exists_isMinOn he (show ContinuousOn (f i j k) K from ((hf j).sub (hf k) |>.norm).continuousOn)
       have hz:0<f i j k x:=norm_pos_iff.mpr (sub_ne_zero.mpr ((hsafe x hx i).ne h))
       exact Filter.mem_of_superset (gt_mem_nhds hz) (fun c hc _ y hy=>(show c< f i j k x from hc).trans_le (hmin hy))
     have h': K=∅:= Set.not_nonempty_iff_eq_empty.mp he
     simp [h,h']
   let D:= 𝓝[>] (0:ℝ)
   obtain ⟨δ,hδ,h⟩:=((eventually_all.mpr fun i=>eventually_all.mpr fun j=>eventually_all.mpr fun k=>he i j k).filter_mono (show D ≤ 𝓝 0 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin |>.exists
   refine ⟨δ,h,fun z hz i j k hj=>hδ i j k hj z hz⟩
lemma normProd_bound {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] [ProperSpace E](g:∀ i:ι,Points (n i)→E→ₗ[ℂ] ℂ)
   (hg:∀i z,Points.cons 0 z∈ conf (n i+1) → ∀ v:E,ContinuousAt (fun p:Points (n i) × E=>g i p.1 p.2) (z,v)):
    ∃A> (0:ℝ),∀z∈K,∀i,∀v:E,‖g i (z i) v‖≤A*‖v‖:=by
    let K':=K ×ˢ (Metric.closedBall (0:E) 1)
    have he(i:ι)(p:((i:ι)→Points (n i)) × E)(hp:p∈K'): ContinuousAt (fun q:((i:ι)→Points (n i)) × E=>‖g i (q.1 i) q.2‖) p:=by
        have hf:=(hg i _ (hsafe p.1 (Set.mem_prod.mp hp).1 i) p.2).comp_of_eq (show Continuous (fun q : ((i:ι)→Points (n i)) × E =>(q.1 i,q.2)) by fun_prop).continuousAt (by rfl); exact hf.norm
    have ht(i): ∃A,∀z∈K,∀v:E,‖g i (z i) v‖≤A*‖v‖:=by
       obtain ⟨a,ha⟩:=(hK.prod (isCompact_closedBall ..)).bddAbove_image (continuousOn_of_forall_continuousAt (he i))
       refine ⟨max 1 a,fun z hz v=>?_⟩; by_cases hv:v=0
       · simp [hv]
       let w:=((‖v‖:ℂ))⁻¹ • v
       have hw: v = (↑‖v‖:ℂ) • w:=by unfold w; rw [← mul_smul]; simp [hv]
       nth_rw 1 [hw]; rw [map_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs, abs_norm, mul_comm]; refine mul_le_mul_of_nonneg_right ((ha ⟨(z,w),⟨hz,?_⟩,rfl⟩).trans (le_max_right ..)) (norm_nonneg _)
       rw [Metric.mem_closedBall,dist_zero_right,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (norm_pos_iff.mpr hv),inv_mul_cancel₀ (norm_pos_iff.mpr hv).ne']; -- done
    choose a ha using ht; obtain ⟨A,hA⟩:=Finite.bddAbove_range a
    exact ⟨max 1 A,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun z hz i v=>(ha i z hz v).trans (mul_le_mul_of_nonneg_right ((hA (Set.mem_range_self _)).trans (le_max_right ..)) (norm_nonneg _))⟩
variable (hw:Note C.S (fun i=>fuga C.path.levels (i+1)) (-1))
local notation "R'" => (fun i:ℕ=> fuga C.path.levels (i+1))
local notation "Yb" => (fun i:ℕ=> topZone C.path.levels (C.S.block i) (i+1))
include hw
omit hK hsafe in
lemma topNote : Note C.S Yb (-1):=by exact ((stepar C.path.levels).mills hw).swapP (by ring)
lemma within_reach :∀ᶠ m in atTop, ∀ (r:ℝ), (R') m ≤ r → r≤(Yb) m → ∀ z∈K,∀ y∈arena r,∀i,slide C.S (m+1) (Points.cons y (Points.cons 0 (z i))):=by
    obtain ⟨δ,hδ,hp⟩:=gapK K hK hsafe
    filter_upwards [((topNote hw).thins (show -(1:ℝ)<0 by norm_num)|>.const_mul 8).eventually (gt_mem_nhds (show 8*(0:ℝ)<δ by simpa using hδ))] with m hm r hr hr' z hz y hy i
    have hb:(1:ℝ)≤ (C.path.levels.budget (m+1)).B := by exact_mod_cast (C.path.levels.budget (m+1)).B_pos
    have hd:=C.S.a_pos (m+1)
    have hw:4*C.S.a (m+1) ≤ r/16:=by change 128*_*(C.S.a _ ) ≤ _ at hr; nlinarith only [hr,mul_le_mul_of_nonneg_right (one_le_pow₀ hb (n:=2)) hd.le,hd]
    let x:=Points.cons (n:=n i) 0 (z i)
    have hj (k:Fin (n i+1)):4*C.S.a (m+1)< ‖x k-y‖∧4*C.S.a (m+1)< ‖y-x k‖:=by
       rw [norm_sub_rev y]; apply and_self_iff.mpr
       refine Fin.cases (?_) (fun k'=>?_) k
       · simpa [x,Points.cons] using (hw.trans_lt hy.1)
       have hx:=hp z hz i k'.succ 0 (Fin.succ_ne_zero _)
       rw [show Points.cons 0 (z i) 0=0 from rfl,sub_zero] at hx
       have hl:= @norm_sub_norm_le _ inferInstance (x k'.succ) y; change _< ‖x k'.succ‖ at hx
       have hpos:0≤r:=by have hh:=Ribbons.fugap C m; exact hh.le.trans hr
       have hy':= hy.2; change _ ≤ (Yb) m at hr'; change 8*(Yb) m < δ at hm; linarith only [hy',hw,hx,hr',hm,hl,hpos]
    intro u u'; refine Fin.cases (Fin.cases (by simp) (fun k'=> fun _=> (hj k').1)) (fun k=> Fin.cases (fun _=>(hj k).2) (fun k' hne => (by
         change 4*C.S.a (m+1) < ‖x k' - x k‖; have hh':=hp z hz i k' k (fun hh=>hne (congrArg Fin.succ hh.symm)); exact hh'.trans' (by change 8*(Yb) m < δ at hm; linarith)))) u u'
open MergeProof.Acme
variable (q:∀i:ι,Fin (n i)→ C.book.Token)
def combo (V B:S.Tag)(c:ι→ℂ)(z:∀i,Points (n i))(y:E4):=∑ i:ι,c i*twice (q i) V B y (z i)
variable (V B:S.Tag)
variable (hc:S.Hierarchy)(hp:F.PointLimits C S)
variable (hq:Cells.CellHyp C F)(hC:C.Makes)
variable {β h s:ℝ} {cost:ℕ→ℝ} {j:ℕ→ℕ} (hm:W.Derivatives S)
include hc hp hC hq
variable (hc':Note C.S cost β)(hs:1<s)(hj:Tendsto j atTop atTop)(hJ:Tendsto (fun m:ℕ=> C.S.scale (j m)/C.S.scale m) atTop (𝓝 s)) (sign:(∀i,Points (n i))→(ι→ℂ)→Prop)
include hc' hj hs hJ
lemma derivativePrice (W:DiffPlan S) (sign_unused : Prop) (hem:C.Makes)
        {u:ι}(b:Axis)(D:ℕ) (hx:V.fst+2+(Clouds (C:=C) (expose∘Fin.cons (α:=fun _=> S.Tag) B (S.classTokens∘q u)):ℝ)-h - β < D*(s-1)):
        ∀ᶠ m in atTop, ∀ r> (0:ℝ), r≤ (Yb) m → (R') m ≤r → ∀z∈K,∀y∈arena r,
   ((R') m)^h * ((C.S.a (j m))^D * ‖twice (q u) (trek W b V D) B y (z u)‖) ≤ cost m:=by
    let v := Fin.cons (α:=fun _ => S.Tag) (trek W b V D) (Fin.cons B (S.classTokens∘q u))
    have hSum:((Clouds (C:=C) (expose∘v)):ℝ)+(-1)*h+ D*(-s)<β:=by
       have h0: ((Clouds (C:=C) (expose∘v)):ℝ) = (V.fst:ℝ)+D+2+Clouds (C:=C) (expose∘Fin.cons (α:=fun _=>S.Tag) B (S.classTokens∘q u)) :=by
           unfold Clouds; change (((∑ i:Fin (n u+2), (((expose∘v) i).fst+2)):ℕ):ℝ) = _; rw [Fin.sum_univ_succ]; push_cast; unfold v; simp only [Function.comp_apply,Fin.cons_succ,Fin.cons_zero]
           rw [show (expose (trek W b V D)).fst= (V.fst+D) from trek_h ..]; push_cast; rfl
       linarith only [hx,h0]
    obtain ⟨l,hl⟩:= exists_nat_gt (((↑(n u):ℝ)+2)*6)
    have hv:= Note.longer (C:=C) (Note.glory (C:=C) v) (1+l)
    have hA:=(((Note.note_a C.S).relay j hj hJ).powerN D)
    have he:=hv.mills hA |>.mills (hw.powr h) |>.outweigh hc' (?_)
    swap
    · linarith only [hSum]
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (Ribbons.maine hC hq hp hc (q:=v) l (by exact_mod_cast hl)),he,within_reach K hK hsafe hw] with m hm' hv hf r hr hy hr' z hZ y hy'
    let a:=((R') m)^h; let b':=C.S.a (j m)^D; change _ * (_ * ‖disc v _‖)≤ _
    have hh:=hm' _ (hf r hr' hy z hZ y hy' u) -- hm' includes generic? check
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (pow_pos (C.S.a_pos (j m)) D).le) (Real.rpow_nonneg ((hw.pos m).le) h)).trans (hv.trans' (by change a*(b' * _) ≤ _* _ *_; rw [show m+1+l=m+(1+l) by omega, mul_comm, mul_comm b']))
-- λ ∑ normalized. Output uses Predicate c.
include hm
lemma fill_estimate (HE:∀ᶠ m in atTop,∀ r, (R') m ≤ r → r≤ (Yb) m → ∀ z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1 → sign z c → ∀ y∈arena r,taper (C.S.a (j m)) y=Set.univ → ‖((R') m)^h • combo q V B c z y‖≤cost m):
    ∃A> (0:ℝ),∀ᶠ m in atTop,∀ r:(ℝ), (R') m ≤ r → r≤ (Yb) m →∀ z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1→ sign z c→ ∀ y∈annulus r, ‖((R') m)^h • combo q V B c z y‖≤ cost m*A:=by
    let u (i:ι):=Fin.cons (α:=fun _=> S.Tag) B (S.classTokens∘q i)
    let L(i:ι):ℝ:=V.fst+2+(Clouds (C:=C) (expose∘u i):ℝ)-h-β
    have hw':Tendsto (fun k:ℕ=>(k:ℝ)*(s-1)) atTop atTop:= Tendsto.atTop_mul_const (sub_pos.mpr hs) tendsto_natCast_atTop_atTop
    obtain ⟨D,hD⟩:= (eventually_all.mpr fun i=> hw'.eventually_gt_atTop (L i)).exists
    obtain ⟨A,hA,HH⟩:= MergeProof.Acme.mars D
    refine ⟨A,hA,?_⟩
    have hpiece := (fun i b=> derivativePrice K hK hsafe hw q V B hc hp hq hC hc' hs hj hJ W True hC (u:=i) b D (hD i))
    have hx: Note C.S (fun m=>arm D*(C.S.a (j m))) (-s):= ((Note.notes C.S _ (arm_pos D)).mills ((Note.note_a C.S).relay j hj hJ)).swapP (by ring)
    have hK':= hx.outweigh (hw.splits (Note.notes C.S 128 (by norm_num))) (by linarith only [hs])
    filter_upwards [HE,eventually_all.mpr fun i=>eventually_all.mpr fun b=>hpiece i b,hK',within_reach K hK hsafe hw] with m he hp' hs' hcG r hr hr' z hz c hm' hsh y hy
    apply HH r (C.S.a (j m)) (cost m) (C.S.a_pos _) ?_ (hs'.trans (by change (R') m/128≤ _; gcongr)) _ (he r hr hr' z hz c hm' hsh) ?_ y hy
    · exact hc'.pos _
    intro b x hx
    let a':= C.S.a (j m); let k:= ((R') m)^h
    let f(j':ℕ)(t:ℝ):=∑ i:ι,k • (c i*(a'^j' • twice (q i) (trek W b V j') B (chord b x a' t) (z i)))
    refine ⟨f,?_,?_,fun t ht=>?_⟩
    · funext t; unfold f combo; simp only [Function.comp_apply, Finset.smul_sum]; simp only [trek,pow_zero,one_smul,a',k]
    · intro j hj' t ht
      exact HasDerivAt.fun_sum (fun i _=> ((MergeProof.Acme.pelts W hc x a' V b hm _ _ t (slide_conf C.S _ (hcG r hr hr' z hz _ (hx _ ht) i)) j).const_mul (c i)).const_smul k)
    apply (norm_sum_le ..).trans
    calc _ ≤ ∑ i:ι, ‖c i‖* cost m:= Finset.sum_le_sum fun i _=>by have hp2:=mul_le_mul_of_nonneg_left (hp' i b r ((hw.pos m).trans_le hr) hr' hr z hz _ (hx _ ht)) (norm_nonneg (c i)); change ‖k • (c i*(a'^D • twice (q i) (trek W b V D) B (chord b x a' t) (z i)))‖ ≤ _; dsimp only [k,a']; rw [norm_smul,norm_mul,norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg (hw.pos m).le h), Real.norm_of_nonneg (pow_nonneg (C.S.a_pos (j m)).le D)]; rw [mul_left_comm]; exact hp2
         _ ≤ cost m:= by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left (hc'.pos m).le hm'
    -- need hc' original shadow
include hK hsafe hm hp hq in
lemma priced (hG:G.Simple)(HE:∀ᶠ m in atTop,∀ r:(ℝ),(R') m ≤ r → r ≤  (Yb) m→∀z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1 → sign z c →∀y∈arena r,taper (C.S.a (j m)) y=Set.univ → ‖((R') m)^h • combo q V B c z y‖≤cost m) (γ:ℝ)(hγ:β< -γ):
     ∃r₀> (0:ℝ),∀ z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1→ sign z c→ ∀y:E4,0< ‖y‖ → ‖y‖ <r₀ → ‖combo q V B c z y‖ ≤ ‖y‖^(-h+γ):=by
     obtain ⟨A,hA,he⟩:= fill_estimate K hK hsafe hw q V B hc hp hq hC hm hc' hs hj hJ sign HE
     let p := -h+γ
     have hp':Note C.S (fun m=> cost m*A/((R') m)^h) (h+β):= ((hc'.mills (Note.notes C.S A hA)).splits (hw.powr h)).swapP (by ring)
     obtain ⟨M,hM⟩:=eventually_atTop.mp (he.and (hp'.outweigh (hw.powr p) (by dsimp [p]; linarith only [hγ])|>.and (hp'.outweigh ((topNote hw).powr p) (by dsimp [p]; linarith only [hγ]))))
     let r₀:=(R') M
     refine ⟨r₀,hw.pos _,fun z hz c hc' hsign y hr hy =>?_⟩
     let r:=‖y‖; have hr':0<r:=hr
     have hex':∃ n:ℕ, fuga C.path.levels (n+M+1) ≤ r:= by
         have hh:=((hw.thins (show -(1:ℝ)<0 by norm_num)).comp (tendsto_add_atTop_nat M)).eventually (ge_mem_nhds hr')
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
     have hT:= hh r hL hr'' z hz c hc' hsign y (show y∈annulus r from ⟨by change r/4<r; linarith,by change r<2*r;linarith⟩)
     rw [norm_smul,Real.norm_of_nonneg (by exact hpos.le)] at hT
     apply ((le_div_iff₀ hpos).2 ((mul_comm ..).le.trans hT)).trans
     change cost m*A/_ ≤ _
     rcases le_total 0 p with h|h
     · exact hu.trans (Real.rpow_le_rpow (hw.pos m|>.le) hL h)
     exact hw'.trans (Real.rpow_le_rpow_of_nonpos hr hr'' h)
end YM.MultipleContact.Local
