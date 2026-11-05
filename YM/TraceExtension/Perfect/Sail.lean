import YM.TraceExtension.Perfect.Blunt
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{η C V σ D A Λ:ℝ}{R:PathData G}{B:Bed}
variable {W:Type}{F:Filter W}{n:W→Side}(x:∀ w,Site (n w))(ht:Tendsto (fun w=>(n w).val) F atTop) (r:W→Bed) (hp:∀ w,Floor (r w) p (n w) η V)(h:0<σ)(hA:0≤ A)(hz:∀ w,(r w).metric.strip σ A)
include ht hp h hA hz
lemma aroma_target (s t:Tit G)(b:Axis): Tendsto (fun w=> fisc (r w) (bGauge s (x w)) (petalPush (x w) b (bGauge t (x w)))) F
   (𝓝 (-∑ i:Axis,∑ j:Axis,inner ℝ (dal s i i j) (mixB t 0 b j))) :=by
 let C (k:G.ColorIndex)(v:PlaqAxes) :ℝ:=(- dal s v.val.1 v.val.1 v.val.2 k)*(mixB t 0 b v.val.2) k-(- dal s v.val.2 v.val.1 v.val.2 k) * (mixB t 0 b v.val.1) k
 have hh : (∑ k:G.ColorIndex,∑ v:PlaqAxes,C k v)= -∑ i:Axis,∑ j:Axis,inner ℝ (dal s i i j) (mixB t 0 b j):=by
    rw [collect_band (fun i j=>inner ℝ (dal s i i j) _) ?_, sum_comm]; swap
    · intro i; have hx : dal s i i i= 0:=by
         ext k; have he := congr_arg (fun z:G.Color=> z k) (dal_swap s i i i); simp only[PiLp.neg_apply] at he; simp only[PiLp.zero_apply]; linarith
      rw [hx,inner_zero_left]
    rw [← Finset.sum_neg_distrib]; apply sum_congr rfl; intro i _; rw[PiLp.inner_apply,PiLp.inner_apply,← sum_add_distrib,← sum_neg_distrib]; apply sum_congr rfl; intro j _; unfold C; rw [dal_swap s i.val.2 i.val.2 i.val.1]; simp only[PiLp.neg_apply]; simp; ring
 simp_rw [← hh]; simp only [harvest _ _ _ _ (hp _)]
 refine tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ (fun j _=>?_)
 have hv(a: Axis): Tendsto (fun w=> petal (x w) b a (bGauge t (x w)) i) F (𝓝 (mixB t 0 b a i)):=by
    refine tendsto_const_nhds.congr' ?_; filter_upwards [stately x ht t 0 b a] with w he; simp only [map_zero,add_zero] at he; exact congr_arg (fun z:G.Color=> z i) he.symm
 have hh (a):= metric_berry x ht r hp s h hA hz a b j i; exact ((hh _).mul (hv _)).sub ((hh _).mul (hv _))
lemma dust_race (X:W→PathData G)(Λ:W→ℝ){σ':ℝ}(g:∀ w,(X w).Bounds p σ' C (Λ w))(he:∀ w,Attached (r w) (X w))(hs:∀ w,Bid.Sworn (r w) (n w) G)(b:Axis):
   Stoke F x (fun w=> ballX (dust p (X w) b (x w))) 0 5 :=by
 refine ⟨fun s t hk=>?_⟩
 let V(s t:Tit G)(w:W) := fisc (r w) (bGauge s (x w)) (petalPush (x w) b (bGauge t (x w)))
 let M(w):= loom₂ (n w) G (ballad s (x w)) (ballad t (x w))
 let U w : loom G (n w):= (∑ i:Axis, elm i (coco i b) (x w)); let W'(w): loom G (n w):= ⟨aroma p (X w) (mist (x w) b), (aroma_gone (g w) (hp w) (he w) (hs w) ..).1⟩
 have hx(w): (U w-W' w).val=dust p (X w) b (x w):=by simp only [dust,U, AddSubmonoidClass.coe_finsetSum, Submodule.coe_sub,elm_y];rfl
 have hh(w): M w (W' w)=V s t w+V t s w:=by change iteratedFDeriv ℝ 2 (ballX (W' w).val) 0 _=_; rw[loom_banks (W' w).property]; exact (aroma_gone (g w) (hp w) (he w) (hs w) (x w) b).2 _ _
 have ht': Tendsto (fun w=> M w (U w)) F (𝓝 (∑ i:Axis,riseB s t i i b)):=by
    refine tendsto_const_nhds.congr' ?_; filter_upwards [eventually_all.mpr fun i=> yellow x ht i b s t hk] with w hv; unfold U M; rw [map_sum]; simp only[hv]
 have hh': Tendsto (fun w=> V s t w+V t s w) F (𝓝 (∑ i:Axis,riseB s t i i b)):=by
    have he:= (aroma_target x ht r hp h hA hz s t b).add (aroma_target x ht r hp h hA hz t s b)
    rw [rise_law]; unfold fcb; simp only [sum_add_distrib,neg_add]; exact he
 have hv:= ht'.sub hh'; rw[sub_self] at hv; refine hv.congr (fun w=>?_)
 rw [← hx]; change _= M w (U w-W' w); rw [map_sub,hh]
end YM.Trace.Perfect
