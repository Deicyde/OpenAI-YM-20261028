import YM.TraceExtension.Wicket.Encore
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n:Side}{k:ℕ}{B:BudgetPoint}
abbrev Acre (n:Side):=Face (Per n)
def wings (i:Site n): Finset (Acre n):= univ.filter (fun p=>i∈touched p)
def lit (p:Acre n)(B:BudgetPoint)(U:Config G n):= Chi.canonical.innerShare (B.threshold/16) (G.chord (faceValue U p))
def dapple(i:Site n)(B:BudgetPoint)(U:Config G n):= ∏ p∈ wings i,lit p B U
variable {U:Config G n} {i:Site n}
lemma warm (h:Healthy (B.threshold/16) {i} U): dapple i B U=1:=by
    unfold dapple; refine Finset.prod_eq_one (fun j hj=>?_); have hC:= B.threshold_pos; apply Chi.to_one
    have hh:=G.chord_nonneg (faceValue U j); have he: G.chord (faceValue U j) ≤ B.threshold/16:= le_of_not_gt fun H=> disjoint_left.mp h (mem_singleton_self _) ((flags_spec ..).mpr ⟨_,(mem_filter.mp hj).2,H⟩)
    exact le_trans (pow_le_pow_left₀ (by positivity) (div_le_one_of_le₀ he (by positivity)) _) (by simp)
lemma dapple_zero (h:¬ Healthy (B.threshold/8) {i} U): dapple i B U=0:=by
    obtain ⟨i',hh,hv⟩:= not_disjoint_iff.mp h; obtain rfl:= mem_singleton.mp hh
    obtain ⟨j,hj,he⟩:= (flags_spec ..).mp hv
    refine prod_eq_zero (mem_filter.mpr ⟨mem_univ _,hj⟩) ?_; by_contra hv'; have ht:= Chi.canonical.chosen_lt _ _ (show 0<B.threshold/16 from by positivity[B.threshold_pos]) hv'; linarith
private def shine (G:Gauge)(x:G.Mat):= Chi.canonical.read (‖x‖^2)
lemma lit_ex (p:Acre n)(B:BudgetPoint)(U:Config G n): lit p B U=shine G ((G.colorScale*(B.threshold/16))⁻¹ • (G.mat (faceValue U p)-1)):=by
    have hc:=G.colorScale_pos; have ht:= B.threshold_pos; unfold lit shine Chi.innerShare; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ (G.colorScale*(B.threshold/16))⁻¹)]; apply congr_arg Chi.canonical.read; unfold Gauge.chord; unfold Gauge.colorScale; ring
private lemma glint_tv(k:ℕ)(G:Gauge): ContDiff ℝ k (shine G):=(Chi.canonical.smooth.comp (contDiff_id.norm_sq ℝ)).of_le (mod_cast le_top)
lemma glint (k:ℕ)(B:BudgetPoint) (p:Acre n):∀ U:Config G n, Chart k (lit p B) U:=by
    intro U; unfold Chart Function.comp; simp_rw [lit_ex]; apply (glint_tv k G).contDiffAt.comp (f:=fun x:Directions G n=>_ • (G.mat (faceValue (increment U x) p)-1))
    obtain ⟨S,hS,H⟩:= atp G k 0 le_rfl; let he:= travel_jets (U:=increment U) (H n U 0 (norm_zero.le)) p.1 (w:=square p.2.val.1 p.2.val.2) le_rfl; exact ((he.analytic.sub contDiffAt_const).const_smul _).of_le le_top
lemma litInv(p:Acre n) : GaugeInvariant (lit p B (G:=G)):=by intro g U; simp [lit,face_gauge]
lemma glaze (p:Acre n)(hz:i∈touched p): touched p ⊆ halo 8 {i}:= by
   intro k hk; have hv:= Work.E01.sep_touched p i hz; rw[separation_comm] at hv; exact halo_spec.mpr ⟨_,mem_singleton_self i,(separation_triangle i p.1 _).trans ((add_le_add hv (Work.E01.sep_touched p _ hk)).trans (by omega))⟩
lemma tuneLit (p:Acre n)(h:p∈wings i)(B:BudgetPoint) : LocalOn (halo 8 {i}) (lit p B (G:=G)):=by
   intro U V hv; have he:= agrees_mono hv (Finset.coe_subset.mpr (glaze p (mem_filter.mp h|>.2))); unfold lit; apply congr_arg (fun Y=> _root_.YM.Push.SectorMeasure.Chi.canonical.innerShare _ (G.chord Y)); refine travel_local _ _ U V ?_; intro j hj hv; exact he j (List.mem_toFinset.mpr hj) (List.mem_toFinset.mpr hv)
lemma uriP (B:BudgetPoint)(P:Support n)(i:Site n)(hp:halo 9 {i} ⊆ P): B.Regular P (dapple i B (G:=G)):=by
    have ho:halo 8 {i}⊆P:= (sprout_mono i (show 8 ≤ (9:ℕ) by norm_num)).trans hp; refine regularAi (fun k U=> ?_) ?_ (fun U=>?_)
    · unfold dapple; apply Finset.prod_congr rfl fun i _=> litInv i k U
    · intro U V hv; refine Finset.prod_congr rfl (fun j hj=> tuneLit j hj B U V (agrees_mono hv (coe_subset.mpr ho)))
    exact contDiffAt_prod (t:=wings i) (f:=fun j x=> lit j B (increment U x)) fun j _=> glint _ B j U
lemma size_wings(i: Site n): (wings i).card ≤ (2+2+1)^4* Fintype.card PlaqAxes:=by
    have he:wings i ⊆ (halo 2 {i})×ˢ (@univ PlaqAxes _):=by
       intro p hp; refine mem_product.mpr ⟨halo_spec.mpr ⟨_,mem_singleton_self i, (separation_comm ..).trans_le (Work.E01.sep_touched p _ (mem_filter.mp hp|>.2)) ⟩,mem_univ _⟩
    apply (card_le_card he).trans; rw [card_product,card_univ]; apply Nat.mul_le_mul_right; exact le_trans (Corona.halo_size ..) (by simp)
private lemma shined (G:Gauge)(k:ℕ)(v:ℝ):∃ C:ℝ,0≤ C ∧ ∀ x:G.Mat, ‖x‖ ≤ v→ Through k (shine G) x C:=by
    let S:=closedBall (0:G.Mat) v
    have h(j) (hj:j≤k):∃ c:ℝ,∀ x:G.Mat,x∈S→‖iteratedFDeriv ℝ j (shine G) x‖≤ c:= (isCompact_closedBall ..).exists_bound_of_continuousOn (f:=iteratedFDeriv ℝ j _) (((glint_tv k G).continuous_iteratedFDeriv (Nat.cast_le.mpr hj)).continuousOn)
    choose! F hf using h; let C:ℝ:=∑ i∈range (k+1),|F i|; refine ⟨C,sum_nonneg fun i _=>abs_nonneg _,fun x hx=>⟨(glint_tv k G).contDiffAt,fun i hi=>?_⟩⟩
    exact (hf _ hi x (by simpa[S] using hx)).trans ((le_abs_self _).trans (single_le_sum (s:=range (k+1)) (f:=fun i=> |F i|) (fun i _=> abs_nonneg _) (mem_range.mpr (by omega))))
lemma bill_lit(G:Gauge)(k q:ℕ) (hk:1≤ k)(T:Collar G k) : ∃ D:ℝ,0≤ D ∧ ∀ (B:BudgetPoint)(h:B.order=k),let J:Collar G B.order:=h.symm ▸ T; B.power=q→ Cube.Wire B 8 J→∀ (n:Side)(p:Acre n),∀ x:Directions G n, ‖x‖≤ Cube.fee J→Through B.order (minor (lit p B) (Cube.moduleBill B 8)) x D:=by
    let A:= Cube.fee T; have ha:1≤ A:= Cube.fee_one T; obtain ⟨S,hS,H⟩:= atp G k A (by positivity)
    let V:= travelCost G k 4 S+‖( -(1:G.Mat))‖
    have h₁(G':Gauge)(k:ℕ)(A:ℝ)(ha:0≤ A): 0 ≤ travelCost G' k 4 A:= travel_non _ _ _ _ ha
    have hv:0 ≤ V:= add_nonneg (h₁ G k S hS) (norm_nonneg _); let W:ℝ:= V*evenR 1 A*16*9^q/G.colorScale; have hψ:= G.colorScale_pos; have hw:0 ≤ W:=by unfold W evenR; positivity
    obtain ⟨C,hC,he⟩:= shined G k W
    refine ⟨composeCost k C W,by unfold composeCost; positivity, fun B h=>?_⟩; subst k; intro J hp hx n p x he'; change ‖x‖≤A at he'
    let s:= Cube.moduleBill B 8; let e(z:Directions G n):= faceValue (increment (1:Config G n) z) p; let L(z:Directions G n):= G.mat (e z) -1
    have hs:0<s:=mul_pos B.threshold_pos (pow_pos (a:= (1:ℝ)+ (↑(8:ℕ):ℝ)) (by positivity) _); have hz(y:Directions G n)(hy:‖y‖≤A): Allows B.order L y V:=by
       have hH := travel_jets (U:= increment (1:Config G n)) (H n 1 y hy) p.1 (w:=square p.2.val.1 p.2.val.2) (show List.length _≤4 from le_rfl)
       unfold L V; simp_rw [sub_eq_add_neg]; exact hH.add (allows_const _ (show ‖- (1:G.Mat)‖ ≤ _ from le_rfl))
    have hl : Allows B.order (fun y=>L (s • y)) x (V*evenR 1 A*s^ (1:ℕ)):=by
       apply heaven 1 A (by positivity) hs.le hx.2 (fun y hy=> hz y (hy.trans (mul_le_of_le_one_right (by positivity) hx.2))) hv hk _ x he'; intro i hi; have hh:i=0:=Nat.lt_one_iff.mp hi
       rw[hh,norm_iteratedFDeriv_zero,show L 0=0 from by simp [L,e,Work.G07.at_zero_increment,WilsonStartup.face_one],norm_zero]; positivity
    let t:=(G.colorScale*(B.threshold/16))⁻¹; let F(y:Directions G n):= t • L (s • y)
    have ht : Allows B.order F x W:= by
        convert! hl.smul t using 1; unfold W t s; have he:=B.threshold_pos; rw[abs_of_pos (by positivity : 0 <(G.colorScale*(B.threshold/16))⁻¹),Cube.moduleBill,hp]; push_cast; field_simp; ring
    unfold minor; simp_rw[lit_ex]; exact (he (F x) ht.value).comp (Through.control ht)
lemma dppaid (G:Gauge)(k q:ℕ)(hk:1≤k)(T:Collar G k): ∃ D:ℝ,0≤D∧∀ (B:BudgetPoint)(h:B.order=k),let J:Collar G B.order:=h.symm ▸ T; B.power=q→ Cube.Wire B 8 J →∀ (n:Side)(o:Site n)(P:Support n), 20<n.val →halo 9 {o}⊆P→ B.supBounds o P (dapple o B (G:=G)) D:=by
    obtain ⟨D,hD,H⟩:= bill_lit G k q hk T; let C:= 1+composeCost k D (Cube.fee T); have hc:1≤C:= le_add_of_nonneg_right (by have h:= Cube.fee_one T; unfold composeCost; positivity)
    let u:ℕ:=(2+2+1)^4* Fintype.card PlaqAxes; refine ⟨((2:ℝ)^k*C)^u,by positivity,fun B h=>?_⟩; subst k; intro j he hv n i P hn ht; refine ⟨by positivity,fun U hx=>?_⟩; let W:= wings i
    have hs(p:Acre n)(hp:p∈ W): Clear B.order (B.dirBound i) U (lit p B) C:=by
        have hu:= tuneLit p hp B (G:=G); have he' : B.Regular P (lit p B (G:=G)):= regularAi (litInv p) (fun U V h=> hu U V (agrees_mono h (Finset.coe_subset.mpr ((sprout_mono _ (show 8≤ (9:ℕ) by omega)).trans ht)))) (fun x=> glint _ B p x)
        have hq := lends (r:=8) he' ht hu (by omega) j hv hD (H B rfl he hv n p); exact ⟨he'.smooth U hx,fun l hl hh=> (hq.2 U hx l hl hh).trans (le_add_of_nonneg_left zero_le_one)⟩
    have hy(u:Finset (Acre n))(h:u⊆W):Clear B.order (B.dirBound i) U (fun x=>∏ j∈u,lit j B x) ((2^B.order*C)^u.card):=by
        induction u using Finset.induction with
        | empty=>simp; exact clear_const (by norm_num)
        | insert i v hx ih=>
          simp_rw [prod_insert hx,card_insert_of_notMem hx,pow_succ',mul_assoc]; exact (hs _ (h (mem_insert_self _ _))).mul (ih ((subset_insert _ _).trans h))
    have h':=hy W (fun _ h=>h)
    intro l h hl; exact (h'.pay l h hl).trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hc) (size_wings i))
end YM.Trace.Wicket
