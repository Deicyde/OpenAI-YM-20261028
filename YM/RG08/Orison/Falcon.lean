import YM.RG08.Orison.Civic

/-! # Infinite primitives as limits on overlapping stages in the exact Ward geometry. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen Rows RG08.Supplies Flat
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {G:Gauge}{a:Levels G}(F:Horizon a){P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{U:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d k:ℕ}
variable (L: Yamen.Supplies F P Z)(hA:Flat.Quorum (Flat.curve X) U 0 F A B d k c)

abbrev poles (m i:ℕ): Kernel (Tack.Head (RG08.Supplies.stone a m) G) (Tack.Head (RG08.Supplies.stone a m) G):=Prism.ice (G:=G) _ a.clock.kernel (F.H i (m+1))
abbrev skies (m i:ℕ): Kernel (Tack.Head (RG08.Supplies.stone a m) G) (Loc G 1):=Prism.rains (G:=G) _ a.clock.kernel (F.H i (m+1))
local notation "j%"=>a.clock.J

include L hA
set_option linter.unusedSectionVars false in
lemma telescope (m :ℕ) :∃ p:ℕ→ℝ,Tendsto p atTop (𝓝 0) ∧ ∀ N N', m ≤ N→N ≤ N'→ RowCost (curve X (j% m)) 1 (Cell.changeK (F.H N' m) (F.H N m)) (p N) ∧ 0 ≤ p N:=by
 let y:=Flat.clock a.S (Lambda' a) m m
 let D:=A*y^d
 have hY:y≥2:= (Yamen.small a 0).age_big (⟨m,m,m,le_rfl,m,by omega⟩:Audience a 0) m
 have hD:D≥0:=mul_nonneg hA.logged (by positivity)
 let f(N):=(a.S.a N /a.S.a m)^c
 refine ⟨fun N=>2*D*f N,rate0 hA.positive _ _,fun i j hi hj=>?_⟩
 have hh (N)(hN:m ≤ N): RowCost (curve X (j% m)) 1 (fun x z=>output (F.H N m) x z-U m x z) (D*f N):= hA.approximates m m N (by omega) hN
 have he (n): 0 ≤ f n:= Real.rpow_nonneg (div_nonneg (a.S.a_pos n).le (a.S.a_pos _).le) _
 have hs:=subtract_row (hh j (hi.trans hj)) (hh i hi) (mul_nonneg hD (he j)) (mul_nonneg hD (he i))
 rw [show (fun x z=> (output (F.H j m) x z-U m x z)-(output (F.H i m) x z-U m x z))= Cell.changeK (F.H j m) (F.H i m) from funext (fun i=>funext (fun z=>by unfold Cell.changeK;ring))] at hs
 have hx:f j ≤ f i:=by unfold f; have hf:= a.S.a_pos j;have hx:= a.S.a_pos m;have h:=hA.positive;gcongr;exact a.S.strictAnti.antitone hj
 refine ⟨fun i z=>(hs i z).trans (ENNReal.ofReal_le_ofReal ?_),?_⟩
 · dsimp only; nlinarith only [mul_le_mul_of_nonneg_left hx hD]
 have h:=he i;dsimp only; positivity

lemma heated (m n:ℕ)(hn:m<n) : let σ:=RG08.Supplies.Strip G P X a.clock.kernel (j% (m+1));0 <σ ∧ Alpine (K:=fun i=>poles F m (i+n)) (N:=land (poles F m)) σ ∧ Alpine (K:=fun i=>skies F m (i+n)) (N:=land (skies F m)) σ:=by -- Alpine explicit args K names?
 obtain ⟨x,hx,H⟩:=telescope F L hA (m+1)
 intro σ;let j:= j% (m+1);let P0:=RG08.Supplies.stone a m;let k:=a.clock.kernel
 let W:= stamp G P X k Z P0
 have hP: 0 < σ:= RG08.Supplies.positive_strip (G:=G) (P:=P) (X:=X) (K:=k) j
 have hθ:σ≤ min (RG08.Supplies.PlanCurve G k P j) (P0.L.val*curve X j):=by
    unfold σ RG08.Supplies.Strip; gcongr; exact le_mul_of_one_le_left (curve_pos ..).le (by exact Nat.one_le_cast.mpr P0.L.property)
 have hf:=Yamen.stamped G P X k Z P0
 have he(i)(hi:m < i): (F.H i (m+1)).metric.strip (P.α j) (P.Ω j):=(L.housed.rows _ _ hi).2.1
 have HT (i j')(h:m < i)(h':i ≤ j'):= Yamen.viable (W:=W) (Q:=P) (warms L.housed i m h) (warms L.housed j' m (lt_of_lt_of_le h h')) (RG08.Supplies.plan_hr ..|>.2.1) (L.housed.all _ _ h) (L.housed.all _ _ (lt_of_lt_of_le h h')) (he _ h) (he _ (lt_of_lt_of_le h h')) (H i j' h h').1 (H i j' h h').2 hP hθ hf.pos hf.plant hf.key hf.allowance (Ω_pos L.housed (m+1))
 refine ⟨hP,terrain (m:=m+1) n hn (fun i=>W*x i) (by simpa using hx.const_mul W) (fun i hi=> (HT i i hi le_rfl).1) (river _ _ _ _ (by simpa using hx.const_mul W) hP.le (fun i hi=> (HT i i hi le_rfl).1) (fun i j hi hj => (HT i j hi hj).2.2.1)),?_⟩
 let C:= 2*W^2
 exact terrain (m+1) n hn (fun i=>C*x i) (by simpa using hx.const_mul C) (fun i hi=> (HT i i hi le_rfl).2.2.2.1) (river _ _ _ _ (by simpa using hx.const_mul C) hP.le (fun i hi=> (HT i i hi le_rfl).2.2.2.1) (fun i j hi hj=> (HT i j hi hj).2.2.2.2.2))

-- output Hessian U also as series. Fat use land via quorum or direct U. T Lin tends via. algebra and cauchy. -/
abbrev alumna (m i:ℕ): Kernel (Loc G 1) (Loc G 1):= Prism.alum G (F.H i m)
lemma pedestal (m n:ℕ)(hn:m ≤ n): ∃ σ:ℝ,0< σ ∧ Alpine (fun i=>alumna F m (i+n)) (land (alumna F m)) σ:=by
 obtain ⟨x,hx,H⟩:= telescope F L hA m
 let j:=j% m;let s:= min (P.α j) (curve X j)
 have ht:0<s:=lt_min (P.alpha_pos _) (curve_pos ..)
 have hQ:s ≤ 1:=by unfold s Flat.curve; exact (min_le_right ..).trans (min_le_left ..)
 let C:=Flat.sumToken*(Fintype.card Faces*P.Ω j)
 have hk(i)(hi:m ≤ i): Priced s C (alumna F m i):=(Prism.certified G (F.H i m) (fun a x=> ((L.housed.rows _ _ hi).2.1 a x).mono (min_le_left ..) le_rfl) ht hQ (Ω_pos L.housed m)).toPriced
 have h1(i k)(hi:m ≤ i)(hj:i ≤ k): Priced s (x i) (alumna F m i-alumna F m k):=by
    obtain ⟨HE,hV⟩:=H _ _ hi hj
    let b:= F.H k m;let v:=F.H i m;let D:=Cell.changeK b v
    have hp: city 1 D := (by intro i j w; exact congrArg₂ (fun x y:ℝ=> x-y) (Cast.light_cities b i j w) (Cast.light_cities v i j w))
    have hD:Priced s (x i) D:=⟨hV,hp,HE.mono (min_le_right ..),Cell.col_of_row hp (HE.mono (min_le_right ..))⟩
    have hr:= (Cell.color_tagged G (Spar.cardDeck hD)).toPriced -- name
    have hS:alumna F m i-alumna F m k= -(Cell.color G D):=by funext ⟨p,a,c⟩ ⟨q,b,d⟩;unfold alumna Prism.alum Cell.color; simp only [Pi.sub_apply,Pi.neg_apply]; split <;> simp [D,Cell.changeK];ring
    exact hS.symm ▸ hr.neg
 exact ⟨_,ht,terrain m n hn x hx hk (river _ _ _ _ hx ht.le hk h1)⟩
end YM.RG08.Orison
