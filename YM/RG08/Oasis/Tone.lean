import YM.RG08.April.Caps
import YM.RG08.Orison.Civic
/-! # Completeness through marked ledgers and offshell Sings. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Oasis
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow April Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
variable {X Z I J:Type}{G:Gauge}{D d e n k:ℕ}{θ:ℝ}{h:0<θ}{L:Jetty.Loom I}

lemma spanCut [Nonempty J](f:I→J→ℝ≥0∞)(s:Finset I): (∑ i∈s, ⨆ j,f i j) ≤ ⨆ v:I→J,∑ i∈s, f i (v i):=by
 induction s using Finset.induction_on with
 | empty=>simp
 | @insert a s ha ih=>
    rw [sum_insert ha];refine (add_le_add_right ih _).trans (ENNReal.iSup_add_iSup_le (fun i v=>?_))
    apply le_iSup_of_le (Function.update v a i)
    rw [sum_insert ha,Function.update_self];exact add_le_add_right (le_of_eq (Finset.sum_congr rfl (fun i hi=>by rw [Function.update_of_ne (by intro H;subst a; exact ha hi)]))) _ -- right
-- Lower semi, price both and diff. no Logs. 
def binge (F:ℕ→Pack n I)(T:Pack n I):Prop:=∀ i f,Tendsto (fun j=>F j i f) atTop (𝓝 (T i f))
lemma binge_cost {F:ℕ→Pack n I}{T:Pack n I}{C:ℝ}(hf:binge F T)(hs:∀ᶠ i in atTop,Sings L d h (F i) C): Sings L d h T C:=by
 apply ENNReal.summable.tsum_le_of_sum_le;intro s
 let J:= {f:Pearl// Jetty.beam d h f≤1}
 letI :Nonempty J:=⟨⟨(0:Pearl),by unfold Jetty.beam;simp⟩⟩
 let f(i:Tape n I)(g:J):=ENNReal.ofReal |T i g.val| *weft L θ i
 have he(i):gems L d h T i ≤ iSup (f i):=by
    unfold gems Jetty.purse; simp_rw [ENNReal.iSup_mul];apply iSup_le; intro u;apply iSup_le; intro hh; exact le_iSup (f i) (⟨u,hh⟩:J)
 apply (sum_le_sum (fun i (_:i∈s)=>he i)).trans ((spanCut f s).trans ?_);apply iSup_le;intro v
 let g(k:ℕ):=∑ i∈s,ENNReal.ofReal (|F k i (v i).val| * Real.exp (θ*L.cage i))
 have H:Tendsto g atTop (𝓝 (∑ i∈s,f i (v i))):=by
    unfold f weft; simp_rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    exact tendsto_finsetSum _ (fun i _=>ENNReal.continuous_ofReal.tendsto _|>.comp ((hf ..).abs.mul_const ..))
 apply le_of_tendsto H (hs.mono (fun k hk=>(le_trans ?_ ((ENNReal.sum_le_tsum (f:=gems L d h (F k)) s).trans hk))))
 apply sum_le_sum;intro i _;rw [ENNReal.ofReal_mul (abs_nonneg _)];apply mul_le_mul_left (purse_unit _ _ (v i).property) -- signature

lemma binge_read {F:ℕ→Pack n I}{T:Pack n I}(he:binge F T)(hp:∀ᶠ i in atTop,Lyrics (F i)∧ ∀ f:Pearl,Forms.Sym (fun i'=>F i i' f)):
 Lyrics T∧ ∀ f:Pearl,Forms.Sym (fun i=> T i f):=by
 constructor
 · intro i; constructor
   · intro x y; exact tendsto_nhds_unique (he i (x+y)) (((he i x).add (he i y)).congr' (hp.mono fun j hj=>((hj.1 i).plus x y).symm))
   intro a x; exact tendsto_nhds_unique (he i (a • x)) ((tendsto_const_nhds.mul (he i x)).congr' (hp.mono fun j hj=> ((hj.1 i).hum a x).symm))
 intro f u;funext i;exact tendsto_nhds_unique (he (i ∘ u) f) ((he i f).congr' (hp.mono fun j hj=> (congrFun (hj.2 f u) i).symm))

def stage (F:ℕ→Pack n I):Pack n I:=fun i f=>if h:∃ v:ℝ,Tendsto (fun m=> F m i f) atTop (𝓝 v) then Classical.choose h else 0
lemma stage_chosen (F:ℕ→Pack n I){i:Tape n I}{f:Pearl}{v:ℝ}(he:Tendsto (fun m=>F m i f) atTop (𝓝 v)):stage F i f=v:=by unfold stage; rw [dif_pos (show ∃ v:ℝ,Tendsto (fun m=> F m i f) atTop (𝓝 v) from ⟨_,he⟩)];apply tendsto_nhds_unique (Classical.choose_spec (show ∃ v:ℝ,Tendsto (fun m=> F m i f) atTop (𝓝 v) from ⟨_,he⟩)) he
lemma stageLimit {F:ℕ→Pack n I}{C:ℝ}{A:ℕ→ℝ}(i:ℕ)(hc:Tendsto A atTop (𝓝 0))(ha:∀ m,i ≤ m→0 ≤ A m)(hh:∀ m,i ≤ m→ Lyrics (F m)∧Sings L d h (F m) C ∧ ∀ f,Forms.Sym (fun j=> F m j f))(hA:∀ m j,i ≤ m→m≤j →Sings L d h (F m-F j) (A m)):
 let T:=stage F
 ; binge F T ∧ Sings L d h T C ∧ Lyrics T ∧ (∀ f,Forms.Sym (fun j=> T j f))∧ ∀ m,i ≤ m→ Sings L d h (F m-T) (A m):=by
 intro T
 have hz(a b)(ha':i≤a)(he:a≤b)(x:Tape n I)(f:Pearl): |F a x f-F b x f|≤ A a*Jetty.beam d h f:= (hA a b ha' he).quote ((hh _ ha').1.sub (hh _ (by omega)).1) (ha a ha') x f
 have hV: binge F T:=by
    intro x f
    obtain ⟨v,hv⟩:=cauchySeq_tendsto_of_complete (cauchySeq_of_le_tendsto_0' (fun j=> A (j+i)*Jetty.beam d h f) (s:=fun j=> F (j+i) x f) (fun j m hj=>by rw [Real.dist_eq];exact hz _ _ (by omega) (by omega) x f) (by convert ((tendsto_add_atTop_iff_nat _).2 hc).mul_const (Jetty.beam d h f);rw [zero_mul])) -- check f argument
    have he:= (tendsto_add_atTop_iff_nat _ (f:=fun m=>F m x f)).1 hv
    rwa [← stage_chosen F he] at he
 have hC:= ((eventually_ge_atTop i).mono hh)
 obtain ⟨hF,hF'⟩:=binge_read hV (hC.mono fun _ h=>⟨h.1,h.2.2⟩)
 refine ⟨hV,binge_cost hV (hC.mono fun _ h=>h.2.1),hF,hF',fun j hj=>binge_cost (F:=fun m=>F j-F m) (fun t f=>tendsto_const_nhds.sub (hV t f)) ((eventually_ge_atTop j).mono (fun m hm=>hA j m hj hm))⟩
end YM.RG08.Oasis
