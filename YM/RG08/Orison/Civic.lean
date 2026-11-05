import YM.RG08.Orison.Boom

/-! # Edges and spot score on bulk, repeated for any fixed level. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {I J:Type}{σ p:ℝ}{K:ℕ→Kernel I J}{N:Kernel I J}
lemma priced_limit (h:∀ x y,Tendsto (fun i=>K i x y) atTop (𝓝 (N x y)))(hp:∀ᶠ i in atTop,Priced σ p (K i)):Priced σ p N:=by
 obtain ⟨i,hi⟩:=Eventually.exists hp;refine ⟨hi.pos,fun x y u=> tendsto_nhds_unique (h _ _) ((h x y).congr' (hp.mono fun j hj=> (hj.city x y u).symm)),?_,?_⟩
 · intro x y;apply ENNReal.summable.tsum_le_of_sum_le; intro s
   exact le_of_tendsto (tendsto_finsetSum s (fun z _=> (ENNReal.continuous_ofReal.tendsto _).comp (((h x (z,y)).abs).mul_const (Real.exp (σ*delta (1:Side) x.1 z))))) (hp.mono fun j hj=> (ENNReal.sum_le_tsum s).trans (hj.row x y))
 intro x y;apply ENNReal.summable.tsum_le_of_sum_le;intro s; exact le_of_tendsto (tendsto_finsetSum s (fun z _=> (ENNReal.continuous_ofReal.tendsto _).comp (((h (z,x) y).abs).mul_const (Real.exp (σ*delta (1:Side) z y.1))))) (hp.mono fun j hj=> (ENNReal.sum_le_tsum s).trans (hj.col x y))

def land (f:ℕ→Kernel I J):Kernel I J:= fun x=> Orison.hope (fun i=>f i x)
def Knit(X:Kernel I J)(V:ℕ→Kernel I J)(σ p:ℝ)(δ:ℕ→ℝ)(m:ℕ): Prop:=(∀ x y,Tendsto (fun i=>V i x y) atTop (𝓝 (X x y))) ∧ Priced σ p X ∧ ∀ i,m ≤ i→Priced σ (δ i) (V i-X)
lemma river {V:ℕ→Kernel I J}(σ p:ℝ)(s:ℕ)(b:ℕ→ℝ)(h:Tendsto b atTop (𝓝 0))(hp:0≤σ)(ht:∀ i,s ≤ i→Priced σ p (V i))(hV:∀ i j,s ≤ i→i ≤ j → Priced σ (b i) (V i-V j)):Knit (land V) V σ p b s:=by
 have H1 i j (h:s ≤ i)(hj:i ≤ j)(q:Market I)(y:Market J):|V i q y - V j q y| ≤ b i:=by
    have hi:=hV i j h hj
    have he: bill (V i q y - V j q y) (σ*delta (1:Side) q.1 y.1) ≤ ENNReal.ofReal (b i):=(ENNReal.le_tsum (f:=fun z=>bill ((V i - V j) q (z,y.2)) (σ*delta (1:Side) q.1 z)) y.1).trans (hi.row q y.2)
    have hh:= (ENNReal.ofReal_le_ofReal_iff hi.pos).mp he
    exact (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hp (delta_nonneg ..)))).trans hh
 have H q y: ∃ v,Tendsto (fun i=>V (i+s) q y) atTop (𝓝 v):=by
    apply cauchySeq_tendsto_of_complete;apply cauchySeq_of_le_tendsto_0' (fun i=> b (i+s)) (fun i j hj=> by rw [Real.dist_eq];exact H1 _ _ (by omega) (by omega) _ _) ((tendsto_add_atTop_iff_nat _).2 h)
 choose v hv using H
 have hh q y:Tendsto (fun i=>V i q y) atTop (𝓝 (v q y)):= (tendsto_add_atTop_iff_nat _).1 (hv q y)
 have hz(q y):land V q y=v q y:=receipt _ _ (hh q y)
 simp_rw [←hz] at hh
 exact ⟨hh,priced_limit hh ((eventually_ge_atTop s).mono (fun _=>ht _)),fun i hi=>priced_limit (K:=fun j=>V i-V j) (fun x y=> tendsto_const_nhds.sub (hh _ _)) ((eventually_ge_atTop i).mono (fun j hj=>hV i j hi hj))⟩

variable [Fintype I][Fintype J]
def Alpine (K:ℕ→Kernel I J)(N:Kernel I J)(σ:ℝ):Prop:=∃ p,hush.cheap p ∧Ducat.Counter (D:=hush) (fun _=>I) (fun _=>J) (fun _=>σ) p K (fun _=>N)
lemma Alpine.narrow (h:Alpine K N p)(he:σ ≤ p): Alpine K N σ:=by
 obtain ⟨d,hd,⟨x,hp,H⟩,h⟩:=h;refine ⟨d,hd,⟨x,hp,fun i=>?_⟩,h⟩
 obtain ⟨ht,hk,hZ⟩:=H i;exact ⟨ht.mono he le_rfl,hk.mono he le_rfl,hZ.mono he le_rfl⟩
lemma terrain {a:ℝ}(m n:ℕ)(hn:m ≤ n)(f:ℕ→ℝ)(h:Tendsto f atTop (𝓝 0))(hp:∀ i,m ≤ i→Priced σ a (K i))(ht:Knit N K σ a f m): Alpine (fun i=>K (i+n)) N σ:=by
 obtain ⟨he,hx,H⟩:=ht
 let g(i):=f (i+n)
 have hg:hush.cheap g:= nicety ((tendsto_add_atTop_iff_nat _).2 h) (fun i:ℕ=> (H (i+n) (by omega)).pos)
 refine ⟨g,hg,⟨_,hush.steady _ (show 0 ≤ max a 1 from zero_le_one.trans (le_max_right ..)),fun i=>?_⟩,hush.steady _ (by positivity)⟩
 exact ⟨(hp _ (by omega)).mono le_rfl (le_max_left ..),hx.mono le_rfl (le_max_left ..),(H (i+n) (by omega)).mono le_rfl (le_mul_of_one_le_left (tiny _ hg i) (le_max_right ..))⟩
end YM.RG08.Orison
