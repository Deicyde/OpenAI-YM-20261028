import YM.RG08.Crown.Tune

/-! # Top invoices and anchor; nontrivial through first two positive orders. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Crown
open Carrel Camera Room Cloud Glyph Function Finset Filter Lattice Rudder Forms Pert.Bulk
open Wilson WilsonStartup Design Exterior Anchor Rudder.Symmetry RG Loop
open scoped ContDiff Topology PowerSeries BigOperators Classical RealInnerProductSpace Matrix
variable {G:YM.Gauge}{P:Side}{n:ℕ}
local notation "o" => (0: Fin 2)
local notation "u" => (Fin.succ (0:Fin 1))

lemma pixels (G:YM.Gauge)(b:Tape 2 G.ColorIndex): pixel G 2 b=if b o=b u then (1/2:ℝ) else 0:=by
 let U(i):=(EuclideanSpace.basisFun G.ColorIndex ℝ i)
 unfold pixel Tensor.coeff
 rw [show (fun i:Fin 2=>(EuclideanSpace.basisFun G.ColorIndex ℝ) (b i))=![U (b o),U (b u)] by ext i:1;fin_cases i <;> rfl]
 have he: iteratedFDeriv ℝ 2 (inK G) 0 ![U (b o),U (b u)]=_:= (inK_low (G:=G)).2.2 (U (b o)) (U (b u)) -- syntax
 rw [smul_apply,he];simp only [U,EuclideanSpace.basisFun_inner,smul_eq_mul]
 split_ifs with h
 · simp [EuclideanSpace.basisFun_apply,h,Nat.factorial]
 simp [EuclideanSpace.basisFun_apply,Nat.factorial];exact h

-- match top through identity metric beams
lemma plume {a b:Finset Axis}(ha:a.card=2)(_hb:b.card=2)(y:Tape 2 G.ColorIndex)(v:Cover): col (hum (prize G 2) y) a b v= if a=b ∧ v=0 ∧ y o=y u then 1/2 else 0:=by
 rw [col,hum] -- protectedR private. expose
 rw [protectedR _ o];
 simp only [lyre,Loop.place,Fin.forall_fin_two,Fin.cons_zero,show (1:Fin 2)=u from rfl,Fin.cons_succ,ha,true_and, ↓reduceIte,pixels]; by_cases h:a=b <;>by_cases h':v=0 <;> simp [h,h',eq_comm (a:=b)]

lemma summers_pour {I J:Type}(S:Finset J)(F:J→Flake n (Market I))(e:Fin n)(hh:∀ i∈S,∃ τ C, 0 ≤τ∧Held (carpet _) τ C (F i)):Isles.pour (P:=P) (S.sum F) e=S.sum (fun i=>Isles.pour (F i) e):=by
 funext x;rw [Isles.pour_at,Finset.sum_apply];simp_rw [Finset.sum_apply]; rw [Summable.tsum_finsetSum]; · simp only [Isles.pour_at]
 intro i hi;obtain ⟨τ,B,hb,h⟩:= hh i hi
 let X:=Isles.lantern e x
 have hz(z : X):z.val e=Isles.reach (x e):=z.property.1
 apply Summable.of_norm
 exact ((Isles.cell_sum h hb e (Isles.reach (x e))).comp_injective (Subtype.val_injective (p:=fun a=>a∈X))).congr (by intro i;simp [comp_apply,hz i,Real.norm_eq_abs])

lemma resupply (G:YM.Gauge)(k n:ℕ)(i:Fin k):∃ τ C:ℝ,0<τ∧ 0≤ C∧ Held (carpet _) τ C (Carrel.completed (prize G k) i n) ∧ Forms.Sym (Carrel.completed (prize G k) i n) ∧ Cohort (Carrel.completed (prize G k) i n):=by
 obtain ⟨D,hD,h⟩:= earned (σ:=1) G k i
 obtain ⟨C,hC,H⟩:=completed_held G n i zero_lt_one
 exact ⟨_,C*D,by have :0<(k:ℝ):=Nat.cast_pos.mpr i.pos; positivity,mul_nonneg hC (zero_le_one.trans hD),H _ (zero_le_one.trans hD) h⟩

theorem nearest (G:YM.Gauge)(P:Side)(n:ℕ)(i:Fin (n+2)):
 tap n (tax 2 (gold G P))=parley (Isles.pour (recitation G n) i):=by
 let V:= recitation G n
 apply MvPolynomial.funext;intro v
 rw [rings G P n i (v:=v),←reading_parley]
 rw [recitation,summers_pour (range (n+3)) _ i,reading_sum]; swap
 · intro j _; split
   · exact ⟨0,0,le_rfl,Forms.zero_held⟩
   obtain ⟨q,b,hq,hb,h,-⟩:=resupply G j (n+2) ⟨0,by rename_i a h;omega⟩
   exact ⟨q,b,hq.le,h⟩
 dsimp only [groupUse];apply Finset.sum_congr rfl;intro j _;split_ifs <;> first|rfl|simp [Carrel.reading,Isles.pour,Set.indicator]
lemma core_top (G:YM.Gauge): Loop.Core (prize G 2) (1/2):=by
 intro i j hi hj y
 unfold Loop.spectrum load AxisK; simp_rw [plume hi hj]; by_cases HH:i=j∧y o=y u
 · simp only [HH.1,HH.2,true_and, and_true,↓reduceIte];simp
 rw [if_neg HH]; simp_rw [show ∀ v:Cover,(if i=j ∧ v=0 ∧ y o=y u then (1/2:ℝ) else 0)=0 from (fun v=>if_neg (fun hv=>HH ⟨hv.1,hv.2.2⟩))];simp

private abbrev R:= YM.Work.F08.unitRow (TypeFace 2)
lemma basement (G:YM.Gauge)(P:Side):Isles.pour (P:=P) (Carrel.completed (prize G 2) o 2) o=(1/2:ℝ) • Cast.arcade (Precision.K 1):=by
 obtain ⟨D,hD,h⟩:= earned (σ:=1) G 2 o
 have ht:prize G 2=(1/2:ℝ) • Cast.beam G (plain R):=by
    -- both grade & plume equality cols suffice from Cohort
    let F:= prize G 2
    apply Cast.compress_inj (k:=2) _ _ Anchor.expand_grade _
    · funext x
      unfold Anchor.compress
      rw [Function.comp_apply,Function.comp_apply, Pi.smul_apply, Cast.beam,Anchor.extend_top (Cast.spur G (plain R))];change prize G 2 (et x)=_; rw [protectedR _ o, pixels]
      simp only [Anchor.et, ec,Function.comp_apply, Fin.forall_fin_two, show (1:Fin 2)=u from rfl,true_and,Cast.spur,plain,R,YM.Work.F08.unitRow];split_ifs <;> simp_all [eq_comm,sub_eq_zero]; rename_i H Y J; exact J (Subtype.ext H.2)
    intro y i x hx; change (1/2:ℝ) • hum _ _ _=_;rw [Anchor.expand_grade y i x hx,smul_zero]
 rw [Carrel.complete_top (prize G 2) o (home _ (by decide) o) h (by linarith) (by positivity),ht,map_smul]
 have he(F:Raw G.ColorIndex 2): Isles.pour (P:=P) (compress 1 ((1/2:ℝ) • F)) o=(1/2:ℝ) • Isles.pour (P:=P) (compress 1 F) o:=by
    ext z;rw [Pi.smul_apply,Isles.pour_at,Isles.pour_at]; change (∑' x:Isles.lantern o z,(1/2:ℝ)*compress 1 F x.val)=_; rw [tsum_mul_left,smul_eq_mul]
 rw [he];congr 1
 have hi : R.strip 1 1:= YM.Work.F08.strip_unit
 have hm: Packets.city 1 (plain R):= Packets.pass_one _
 have hv:= Cast.spur_cost (G:=G) (plain0 hi le_rfl).1 (plain0 hi le_rfl).2 zero_le_one zero_le_one
 apply Eq.trans (Cast.picture_arcade ( Pert.Bulk.matches_plain R) (NextTo.unit zero_lt_one (by unfold Cast.tax; positivity) (Anchor.expand_path (Cast.spur_path hm)) (Anchor.expand_cost hv) (Fin.pos o)))
 rw [YM.Work.F08.acts_unit]

-- low positive order coefficient check in exp(g log) at Wilson input, verifies cubic entirely
-- from nonlinear completion of plaquette leading (no extra packet), and k=2 (quartic) directly
-- from same plus fixed color panel. (noise omitted at exact top; contributes in following
-- blocking, not part of start stencil).
theorem twoOrders (G:YM.Gauge):
 recitation G 0 = Carrel.completed (prize G 2) o 2 ∧ recitation G 1=Carrel.completed (prize G 2) o 3 ∧ recitation G 2= Carrel.completed (prize G 2) o 4+Carrel.completed (prize G 4) 0 4:=by
 unfold recitation;norm_num [Finset.sum_range_succ,Nat.odd_iff]

end YM.RG08.Crown
