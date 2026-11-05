import YM.RG08.Apex.Song
import Mathlib.Analysis.Matrix.Order
/-! # Limiting periodized covariance remains full-rank, not merely a
 spectral limit on a shrinking patch. Adjacent law for the primitives. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Summit
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free Matrix Tree
open scoped BigOperators Topology Real Classical Matrix.Norms.Frobenius
open Chain Wings
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {I : Type} {u : I→Windows} {r e : ℕ} {c f : Side}

lemma arrivesRow {α β : Type} [Fintype α] [Fintype β] {R : ℕ→ Row α β}{V : Row α β}{y w : ℝ}{δ:ℕ→ℝ}(h : RowBoth (fun _=>y) δ R (fun _=>V) (fun _=>w)) (hw : 0<w)(hp: Tendsto δ atTop (𝓝 0))(he:0 ≤ δ)(m) : Tendsto (fun i=>(R i).acts m) atTop (𝓝 (V.acts m)) := by
  obtain ⟨A,⟨C,p,hC,H⟩,hv⟩:=h.moves; have ht : Tendsto R atTop (𝓝 V) := by
    refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mpr fun k=> tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun _=> norm_nonneg _) (g:=fun i=> C*y^p*δ i) (fun s=>?_ ) (by simpa using hp.const_mul (C*y^p))
    exact ((le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (mul_nonneg hw.le (Nat.cast_nonneg _)))).trans (budget_single (hv s i j) k)).trans (mul_le_mul_of_nonneg_right (H s).2 (he s))
  obtain ⟨B,⟨U,l,hℓ,hk⟩,hP⟩:= h.fresh; have hh : ∀ᶠ i in atTop,(R i).strip w (U*y^l):=.of_forall fun i=> strip_mono (hP i) le_rfl (by rw [Pi.one_apply,mul_one]; exact (hk i).2)
  exact acts_limit (reported ht hh) hh hw m
private lemma gradUp (t : Launch u) (X : Chain) : Tendsto (fun i=> chop X (1/4) (up (escalates t i))) atTop (𝓝 0) :=
    (tendsto_gain X.S (v:=1/4) (by norm_num) (t.i+1)).comp ((show StrictMono (fun i=>t.i+1+i) from fun _ _ hh=>by simpa using hh).tendsto_atTop)

lemma tendK (t : Launch u)(h : Circuit S ν D u)(m : Side) : Tendsto (fun i=>(X.K₀ (escalates t i).N t.i).acts m) atTop (𝓝 ((quarry X t.i).acts m)) ∧ Tendsto (fun i=>(X.K₀ (escalates t i).N (t.i+1)).acts m) atTop (𝓝 ((quarry X (t.i+1)).acts m)) := by
  refine ⟨arrivesRow (V:=quarry X t.i) (R:=fun i=>X.K₀ (escalates t i).N t.i) (y:=t.farY X) (w:=g.w (X.J t.i)) (δ:=fun i=> chop X (1/4) (escalates t i)) ((kernel_pay h).mold (fun i=>low (escalates t i))) (g.pos _) (bye X t) (fun _=> (gain_pos ..).le) _,arrivesRow (V:=quarry X (t.i+1)) (R:=fun i=>X.K₀ (escalates t i).N (t.i+1)) (w:=g.w (X.J (t.i+1))) (y:=(up (escalates t 0)).menu X) (δ:=fun i=> chop X (1/4) (up (escalates t i))) ((kernel_pay h).mold (fun i=>up (escalates t i))) (g.pos _) (gradUp t X) (fun _=> (gain_pos ..).le) _⟩
lemma quarry_comm (t : Launch u)(h:Circuit S ν D u) (m:Side): ((quarry X t.i).acts m)ᵀ=(quarry X t.i).acts m:= by
  have hv := (tendK t h m).1
  ext i j; exact tendsto_nhds_unique_of_eventuallyEq (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv j) i) (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hv i) j) (.of_forall (fun u=> by dsimp only; rw [sym_acts]; exact congr_fun₂ (k_symmetric (X.metric_sym ..)) i j))

lemma quarry_whole (t:Launch u)(h:Circuit S ν D u): Whole (quarry X t.i) := (kernel_pay h).again.status (fun _=>g.pos _) (low (escalates t 0))
lemma quartz_prices (t:Launch u)(h:Circuit S ν D u) : quartz X G t.i=quad G (quarry X t.i) := by
  have ht:=lyric_rate t h; obtain ⟨w,D',hw,H⟩:= quarry_whole t h
  have hp i: Tunable (orbit X (low (escalates t i)) (G:=G)) := (X.high_stocks ν ..).1
  -- limit rate directly `quad_sub` and matching symmetric, no eval limit necessary
  let R := low ∘ escalates t
  have hP (m:Side): ((quarry X t.i).acts m)ᵀ=(quarry X t.i).acts m := quarry_comm t h m
  have hg := (kernel_pay h).mold (fun i=> low (escalates t i)); obtain ⟨A,⟨D,p,hD,hA⟩,H'⟩:=hg.moves
  have he : Mending (fun i=>orbit X (R i)) (quad G (quarry X t.i)):= by
    let δ i:= chop X (1/4) (escalates t i)
    let C:=D*(t.farY X)^p
    refine ⟨⟨_,_,hw, (quad_matches G _ H hw.le hP).1⟩,g.w (X.J t.i), fun i=> qCap G 1 * (C*δ i),g.pos _,by simpa [δ] using ((bye X t).const_mul C).const_mul (qCap G 1), fun i=> ?_⟩
    let N:=(escalates t i).N; let U:= X.K₀ N t.i
    have hs : (U-quarry X t.i).strip (g.w (X.J t.i)) (C*δ i) := strip_mono (H' i) le_rfl (mul_le_mul_of_nonneg_right (hA _).2 (gain_pos ..).le)
    change Glow (quad G U-quad G (quarry X t.i)) _ _
    rw [show _-_ = quad G (U-quarry X t.i) from Eq.symm (quad_sub _ (X.k_whole ..) (quarry_whole t h))]
    have hm m : ((U-quarry X t.i).acts m)ᵀ=(U-quarry X t.i).acts m:= by change ((minusRows U _).acts m)ᵀ=(minusRows U _).acts m; rw [show (minusRows U _).acts m=(X.K₀ N t.i).acts m - (quarry X t.i).acts m from (X.k_whole ..).less (quarry_whole t h) _,Matrix.transpose_sub,hP, sym_acts,k_symmetric (X.metric_sym ..)] -- signature
    apply glow_less (quad_matches G _ hs (g.pos _).le hm|>.1) le_rfl; unfold qCap; exact le_of_eq (by ring)
  exact tendsto_nhds_unique ht.played he.played

variable {α β θ : Type}
private lemma mul_through [Fintype β]{U:ℕ→Matrix α β ℝ}{V:ℕ→ Matrix β θ ℝ}{F : Matrix α β ℝ}{H:Matrix β θ ℝ}(h : Tendsto U atTop (𝓝 F))(he:Tendsto V atTop (𝓝 H)) : Tendsto (fun i=> U i*V i) atTop (𝓝 (F*H)) :=
   tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>tendsto_finsetSum _ fun k _=> (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) k).mul (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp he k) j)
private lemma real_partial [Fintype α][DecidableEq α] (U : ℕ→ Matrix α α ℝ) {V H:Matrix α α ℝ} (h : ∀ i, PosDef (U i))(hp:Tendsto U atTop (𝓝 V))(he:Tendsto (fun i=>(U i)⁻¹) atTop (𝓝 H)) : V.PosDef ∧ H=V⁻¹:= by
    have hH : V*H=1:= tendsto_nhds_unique_of_eventuallyEq (mul_through hp he) tendsto_const_nhds (.of_forall (fun i=> mul_nonsing_inv (U i) ((Matrix.isUnit_iff_isUnit_det ..).mp (h i).isUnit)))
    have ht : ∀ i j, V i j=V j i := by
      intro i j; exact tendsto_nhds_unique_of_eventuallyEq (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hp i) j) (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hp j) i) (.of_forall (fun u=> congr_fun₂ (h u).1 j i))
    have hV : V.PosSemidef:= by
      apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; refine ⟨?_ ,fun x=>?_⟩
      · ext i j; exact ht j i
      have hh : Continuous (fun w:Matrix α α ℝ=> star x ⬝ᵥ(w*ᵥx)):= by unfold dotProduct Matrix.mulVec; fun_prop
      exact ge_of_tendsto' (hh.continuousAt.tendsto.comp hp) (fun i=> (h i).posSemidef.dotProduct_mulVec_nonneg x)
    exact ⟨hV.posDef_iff_isUnit.mpr (IsUnit.of_mul_eq_one _ hH),(Matrix.inv_eq_right_inv hH).symm⟩

-- unitDirection

def poleM (G : Gauge)(X : StepData c f)(T : Forest X.ratio)(M : KRow) :=
    let I:= sprig X T G
    Iᵀ*tensor G (M.acts f+X.kernel.penalty • ((probe X)ᵀ*probe X))*I
lemma pole_history (G : Gauge)(X : StepData c f)(T : Forest X.ratio){M:FreeResolvent.FaceRow}(h:Whole M): treeMatrix G X T M= poleM G X T (hessian M):= by unfold poleM; rw [hessian_acts h]; exact (insertion.compress ..).symm
private lemma tend_tensor {U : ℕ→ Matrix (Body 1 f) (Body 1 c) ℝ} {V} (h:Tendsto U atTop (𝓝 V)) : Tendsto (fun i=> tensor G (U i)) atTop (𝓝 (tensor G V)) := by
   apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; by_cases he : i.2.2=j.2.2
   · simp only [tensor,Matrix.of_apply,he,↓reduceIte]; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h _) _
   simp only [tensor,Matrix.of_apply,he,↓reduceIte]; exact tendsto_const_nhds
lemma tendPrimitive (t:Launch u)(h:Circuit S ν D u)(hv:X.Wake G)(m) : Tendsto (fun j=> Row.acts (curve G X (escalates t j).N t.i) m) atTop (𝓝 ((slate X G t.i).acts m)) ∧ Tendsto (fun j=> Row.acts (predict G X (escalates t j).N t.i) m) atTop (𝓝 ((amber X G t.i).acts m)) :=
  ⟨arrivesRow (y:=t.farY X) (V:=slate X G t.i) (R:=fun i=>curve G X (escalates t i).N t.i) (w:=ticketW P (X.J t.i)) (δ:=fun i=> chop X (1/4) (escalates t i)) ((smooth h hv).mold (escalates t)) (ticket_pos ..) (bye X t) (fun _=> (gain_pos ..).le) _, arrivesRow (y:=t.farY X) (V:=amber X G t.i) (R:=fun i=>predict G X (escalates t i).N t.i) (w:=ticketW P (X.J t.i)) (δ:=fun i=> chop X (1/4) (escalates t i)) ((polishes h hv).mold (escalates t)) (ticket_pos ..) (bye X t) (fun _=> (gain_pos ..).le) _⟩
lemma frozen (t:Launch u)(h : Circuit S ν D u)(hs:X.Wake G)(he:f.val=c.val*(X.S.block t.i).val) :
    let P:=X.pair t.i c f he; let V:= quarry X (t.i+1); let T:= (X.trees t.i).forest P.ratio
    let Z:= poleM G P T V; let p:= unitSplit G P 1
    (slate X G t.i).acts c=repackM p p (sprig P T G * Z⁻¹ * (sprig P T G)ᵀ) ∧ Z.PosDef ∧ (amber X G t.i).acts c=P.kernel.penalty • ((slate X G t.i).acts c * (Row.acts (probeRow G (X.patch t.i) X.kernel) c)ᵀ) := by
  intro Y V T Z p
  let N j:=(escalates t j).N; let M j:=X.metric (N j) (t.i+1)
  let J j:= treeMatrix G Y T (M j); let Q j:= (curve G X (N j) t.i).acts c; let B:= (slate X G t.i).acts c
  let U:=sprig Y T G
  have hf i: J i=poleM G Y T (X.K₀ (N i) (t.i+1)):= pole_history _ _ _ (X.metric_whole ..)
  have hp : Tendsto J atTop (𝓝 Z):= by
    have ht:= mul_through (mul_through (tendsto_const_nhds (x:=Uᵀ)) (tend_tensor (G:=G) ((tendK t h f).2.add_const (Y.kernel.penalty • ((probe Y)ᵀ*probe Y))))) (tendsto_const_nhds (x:=U))
    exact ht.congr' (.of_forall fun i=> (hf i).symm)
  obtain ⟨hQ,hB⟩:= tendPrimitive t h hs c; change Tendsto Q atTop (𝓝 B) at hQ
  have hh i:= slice_compute (k:=X.kernel) (P:=X.patch t.i) (X.trees t.i) (X.history (N i) (t.i+1)) (hs _) c f he; have hP i : PosDef (J i):= (hh i).2.2.1
  have hu i : Q i=repackM p p (U*(J i)⁻¹*Uᵀ):= by apply (hh i).1.trans; unfold FreeResolvent.covariance treeInverse resolve; rw [zero_smul,add_zero]; rfl
  let W:= repackM p.symm p.symm B; let H:=Uᵀ*W*U
  have hJ i : Uᵀ*repackM p.symm p.symm (Q i)*U=(J i)⁻¹:= by
    have h' : repackM p.symm p.symm (Q i)=U*(J i)⁻¹*Uᵀ:= by rw [hu]; ext i j; simp [repackM]
    rw [h']; have hm : Uᵀ * U=1:= insertion.orthogonal (plant T) (plant_inj _)
    simp only [Matrix.mul_assoc]; rw [hm, Matrix.mul_one, ← Matrix.mul_assoc, hm,Matrix.one_mul]
  have hH : Tendsto (fun i=> (J i)⁻¹) atTop (𝓝 H):= by
    have hv : Tendsto (fun i=>repackM p.symm p.symm (Q i)) atTop (𝓝 W):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hQ _) _
    exact (mul_through (mul_through (tendsto_const_nhds (x:=Uᵀ)) hv) (tendsto_const_nhds (x:=U))).congr' (.of_forall hJ)
  obtain ⟨hx,hA⟩:= real_partial J hP hp hH; rw [hA] at hH
  refine ⟨tendsto_nhds_unique_of_eventuallyEq hQ ?_ (Eventually.of_forall hu),hx,tendsto_nhds_unique_of_eventuallyEq hB ?_ (Eventually.of_forall (fun i=> (hh i).2.2.2.1))⟩
  · have ht:= mul_through (mul_through (tendsto_const_nhds (x:=U)) hH) (tendsto_const_nhds (x:=Uᵀ)); exact tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ht _) _
  exact Tendsto.smul tendsto_const_nhds (mul_through hQ tendsto_const_nhds)

def flank (Y : StepData c f)(A:Matrix (Body 1 f) (Body 1 f) ℝ) (u:Link G f)(x:Link G c) := let Q:=tensor G (probe Y); let y := x-Q*ᵥu; u ⬝ᵥ(tensor G A*ᵥu) + Y.kernel.penalty * (y ⬝ᵥ y)
private lemma flank_on (Y : StepData c f)(A:FreeResolvent.FaceRow)(u : Link G f)(x:Link G c) : bedOper Y A u x=flank Y (Precision.K (A.acts f)) u x:= by
    change _ ⬝ᵥ (patron G _ *ᵥ u) + _*((x-patron G _ *ᵥ u) ⬝ᵥ (x-patron G _ *ᵥ u))=_; rw [tensor_same,tensor_same]; rfl
private lemma mat_tap {α β: Type}[Fintype β]{X:ℕ→Matrix α β ℝ}{Y}{P : ℕ→(β→ℝ)}{F}(h:Tendsto X atTop (𝓝 Y))(hp:Tendsto P atTop (𝓝 F)) : Tendsto (fun i=> X i*ᵥP i) atTop (𝓝 (Y*ᵥF)) := tendsto_pi_nhds.mpr fun i=> tendsto_finsetSum _ fun j _=> (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) j).mul (tendsto_pi_nhds.mp hp j)
private lemma mat_dot {α: Type}[Fintype α]{X Y:ℕ→α→ℝ} {U V}(h:Tendsto X atTop (𝓝 U))(hp:Tendsto Y atTop (𝓝 V)) : Tendsto (fun i=> X i ⬝ᵥ Y i) atTop (𝓝 (U ⬝ᵥ V)):= tendsto_finsetSum _ fun i _=> (tendsto_pi_nhds.mp h i).mul (tendsto_pi_nhds.mp hp i)
lemma frozen_cross (t:Launch u)(h:Circuit S ν D u)(hs:X.Wake G)(he:f.val=c.val*(X.S.block t.i).val) :
    let Y:=X.pair t.i c f he; let T:=(X.trees t.i).forest Y.ratio
    ∀ v (x : Active G T→ℝ), flank Y ((quarry X (t.i+1)).acts f) ((installed Y.ratio (amber X G t.i)*ᵥ v)+sprig Y T G*ᵥ x) v = v ⬝ᵥ(tensor G ((quarry X t.i).acts c)*ᵥ v)+dotProduct x (poleM G Y T (quarry X (t.i+1))*ᵥ x) := by
  intro Y T v x
  let i:= t.i; let N j:= (escalates t j).N; let U j:= (X.K₀ (N j) (t.i+1)).acts f; let V j:= (X.K₀ (N j) i).acts c
  let Q j:= installed Y.ratio (predict G X (N j) i); let y:= installed Y.ratio (amber X G i)
  let J j:= poleM G Y T (X.K₀ (N j) (t.i+1)); let W j:= flank Y (U j) (Q j*ᵥ v+sprig Y T G*ᵥ x) v
  let b j:= v ⬝ᵥ(tensor G (V j)*ᵥ v)+dotProduct x (J j*ᵥx)
  have hh j: W j=b j:= by
    have hu : Q j=riseM Y G T (installed Y.ratio (X.A₀ (N j) t.i)):= predict_truth G hs (N j) t.i (escalates t j).cut _ _ he
    unfold W b U V J; rw [hu,sym_acts,sym_acts,← flank_on, bed_gather (V:=X.metric (N j) i), tensor_same, show treeMatrix G Y T (X.metric (N j) (t.i+1))=poleM G Y T (X.K₀ (N j) (t.i+1)) from pole_history _ _ _ (X.metric_whole ..)]
    · exact X.canonical _ t.i (escalates t j).cut he
    exact X.metric_sym ..
  have hQ : Tendsto Q atTop (𝓝 y):= tendsto_pi_nhds.mpr fun u=> tendsto_pi_nhds.mpr fun z=> tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendPrimitive t h hs c).2 _) _
  have ht:= (tendK t h f).2; have hJ: Tendsto J atTop (𝓝 (poleM G Y T (quarry X (t.i+1)))) := mul_through (mul_through (tendsto_const_nhds (x:=(sprig Y T G)ᵀ)) (tend_tensor (G:=G) (ht.add_const (Y.kernel.penalty • ((probe Y)ᵀ*probe Y))))) (tendsto_const_nhds (x:=sprig Y T G))
  have hv:= (mat_tap hQ (tendsto_const_nhds (x:=v))).add_const (sprig Y T G*ᵥx)
  have hz:= (tendsto_const_nhds (x:=v)).sub (mat_tap (tendsto_const_nhds (x:=tensor G (probe Y))) hv)
  apply tendsto_nhds_unique_of_eventuallyEq (f:=W) (g:=b) (Tendsto.add (mat_dot hv (mat_tap (tend_tensor ht) hv)) ((mat_dot hz hz).const_mul Y.kernel.penalty)) (Tendsto.add (mat_dot tendsto_const_nhds (mat_tap (tend_tensor (tendK t h c).1) tendsto_const_nhds)) (mat_dot tendsto_const_nhds (mat_tap hJ tendsto_const_nhds))) (.of_forall hh)
end YM.RG08.Summit
