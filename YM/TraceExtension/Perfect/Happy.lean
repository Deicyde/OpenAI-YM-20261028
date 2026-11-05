import YM.TraceExtension.Perfect.Atta
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {P:Patch}{Z:KernelChoices}{p:Clip}{G:Gauge}{μ A α B D H u v C:ℝ}{f:Side} {V:Type}{F:Filter V}{n:V→Side}
/-- Caps at one gauge. Momentum coupon includes little-o until root stays. -/
structure Saving (F:Filter V)(K:∀ w,Dart G (n w))(u:ℝ)(d e:ℕ→ℝ) : Prop where
 heart (a b)(x) (k:ℕ)(hk:k≤4)(hp:2≤k): Ear F x (fun w=>ballX ((K w).J a b (x w))) u k (d k)
 palm (a x) k (hk:k≤4)(hp:2≤k): Ear F x (fun w=>bottom ((K w).Y a (x w))) u k (d k)
 plum (a x) k (hk:k≤4)(hp:2≤k): Ear F x (fun w=>ballX ((K w).E a (x w))) u k (e k)
 plumQ (a x) k (hk:k≤4)(hp:2≤k): Ear F x (fun w=>ballX ((K w).Q a (x w))) u k (d k)
 mint (a b j x) k (hk:k≤4)(hp:2≤k): Ear F x (fun w=>ballX ((K w).twist a b j (x w))) u k (d k)
 ox (a b x): Tip F x (fun w=>ballX ((K w).J a b (x w))) (fun s t=>north s t 0 a b) 4
 orb (a x): Tip F x (fun w=>bottom ((K w).Y a (x w))) (missY a) 5
 flag (a x): Tip F x (fun w=>ballX ((K w).E a (x w))) 0 5

lemma hMain (P:Patch): (Sheaf.main P.L).radius ≤ 140*P.L.val∧(Sheaf.main P.L).debt ≤ Tour.allSheaf ∧ (Sheaf.main P.L).gold=1:=by
 obtain ⟨h,p,v⟩:=Sheaf.fee_main P.L; exact ⟨by omega,p.trans (by norm_num[Tour.allSheaf]),v⟩
lemma hFlux (P:Patch)(a:Axis): (Sheaf.flux P.L a).radius ≤ 140*P.L.val∧(Sheaf.flux P.L a).debt ≤ Tour.allSheaf ∧ (Sheaf.flux P.L a).gold=1:=by
 obtain ⟨h,p,v⟩:=Sheaf.fee_flux P.L a; exact ⟨by omega,p.trans (by norm_num[Tour.allSheaf]),v⟩
lemma hLeaf (P:Patch)(a:Axis): (Sheaf.leafEdge P.L a).radius≤140*P.L.val ∧ (Sheaf.leafEdge P.L a).debt ≤ Tour.allSheaf:=by
 obtain ⟨h,p⟩:=Sheaf.fee_leaf P.L a; exact ⟨by omega,p.trans (by norm_num[Tour.allSheaf])⟩
lemma hTrace (P:Patch)(a:Axis): (Dart.trace P.L a).radius ≤ 140*P.L.val ∧ (Dart.trace P.L a).debt ≤ Tour.allSheaf:=by
 obtain ⟨h,p,hx⟩:= (Sheaf.trail (A:=ℝ) P.L a).choose_spec; exact ⟨h,p.trans (by norm_num[Tour.allSheaf])⟩

structure PayGrade (G:Gauge)(v C:ℝ) : Prop where
 J (f:Side) (x:Site f) a b k :
    k≤4→cost (landW (f:=f) x) v 4 0 (leaf (ballX (born (G:=G) x a b)) 0 k)≤C
 Y (f:Side) (x:Site f) a k : k ≤ 4 →cost (landW (f:=f) x) v 4 0 (leaf (bottom (mist (G:=G) x a)) 0 k)≤ C
lemma paid_grade (G:Gauge):∃ a C,0<a∧ 0≤C∧∀ v:ℝ,0≤v→v≤a→ PayGrade G v C:=by
 obtain ⟨a,C,h,p,H⟩:= hatchX G 4; refine ⟨a,C,h,p,fun v hv hx=> ⟨fun f x b i k hk=> (H v hv hx k hk f x b i).1,fun f x a k hk=> (H v hv hx k hk f x a 0).2⟩⟩

variable {X:V→ Slide G P Z p μ A α B} {K:∀ w:V,Dart G (X w).f} {d e Q E :ℕ→ℝ} (h0:∀ w,(K w).Sound (X w).b p) (h:LotFee F X u v H D)(s:Saving F K v d e) (hb:Bank H D P.L C d Q e E)(hp:PayGrade G v C)(hx:0≤ C)
include h0 h s hb
local notation "M!"=> Sheaf.main P.L
set_option quotPrecheck false
local notation "K!"=> fun w=> Dart.down (X w).wood (X w).ρ (K w) (X w).t P.L
private lemma fine_hot:Tendsto (fun w=> (X w).f.val) F atTop:=by
 apply tendsto_atTop_mono (f:=fun w=> (X w).c.val) _ h.quiet; intro i; have he:= (X i).s; let r:=(X i).s.ratio; change (X i).c.val ≤ (X i).f.val; apply le_trans _ (le_of_eq r.exact_size.symm); exact Nat.le_mul_of_pos_right _ r.count.property
include hp hx
private lemma save_j (i j:Axis)(k:ℕ)(hk:2≤k)(hy:k≤4)(S:Sheaf)(hs:S.radius≤140*P.L.val)(he:S.debt ≤ Tour.allSheaf)(x:∀ w,Site (X w).c): Ear F x (fun w=>ballX (Dart.hum (X w).wood (X w).ρ P.L S 4 ((K w).J i j) (x w))) u k (Q k/3):=by
 let J:= fun w=> (K w).J i j; let f(w:V):= (X w).f
 have ht:= tourS (X:=X) (J:=J) fun w x=>(h0 w).heart i j x; let H:= fun w:V=> bornT (f:=f w) i j (G:=G)
 change Ear F x (fun w=>ballX (Dart.hum (X w).wood (X w).ρ P.L S 4 (J w) (x w))) u k _
 simp_rw[drips (J:=J) (X:=X) x]
 rcases eq_or_lt_of_le hk with h₀|h₀
 · subst k; exact wind h x hb _ ht (s.ox i j) (tourS (X:=X) (J:=H) fun w x=> born_home ..) (fun x=>⟨fun i=>(loom_read (born_home ..)).2.2, verdant _ (fine_hot h0 h s hb) i j⟩) (fun x=>⟨fun i=>(loom_read (born_home ..)).2.2,earns.eventually (Eventually.of_forall fun w=>hp.J (f w) (x w) i j 2 (by decide))⟩) (fun x=>s.heart i j x 2 (by decide) le_rfl) _ hs he hx
 exact (windB h x hb ht k h₀ hy 4 (by decide) S hs he).1 (fun x k hk hh=> s.heart i j x k (hk.trans hy) hh)

private lemma save_y (i:Axis)(k:ℕ)(hk:2 ≤ k)(hy:k≤4)(x:∀ w,Site (X w).c): Ear F x (fun w=>bottom ((K! w).Y i (x w))) u k (Q k/3):=by
 let J:=fun w=> (K w).Y i; let f(w):=(X w).f; let H:= fun w:V=>fun x:Site (f w)=>mist (G:=G) x i
 obtain ⟨he,hS,hx'⟩:= hMain P; have ht:= tourY (X:=X) (K:=J) (fun w x=> (h0 w).palm i x)
 change Ear F x (fun w=>bottom (Dart.mel (X w).wood (X w).ρ (X w).t P.L (Sheaf.main P.L) (J w) (x w))) u k _; simp_rw [dropY (K:=J) x]
 rcases eq_or_lt_of_le hk with h₀|h₀
 · subst k; exact windY h x hb _ (miss_zero i) ht (s.orb i) (tourY (X:=X) (K:=H) fun w x=> mist_home ..) (fun x=>⟨fun j=> (rain_read (mist_home ..)).2.2.1, varsity _ (fine_hot h0 h s hb) i⟩) (fun x=>⟨fun j=>(rain_read (mist_home ..)).2.2.1,earns.eventually (Eventually.of_forall fun w=>hp.Y (f w) (x w) i _ (by decide))⟩) (fun x=> s.palm i x _ (by decide) le_rfl) _ he hS hx
 exact (windB h x hb ht k h₀ hy 5 (by decide) _ he hS).1 (fun x k hk hh=> s.palm i x k (hk.trans hy) hh)

lemma save_step : Saving F K! u Q E:=by
 have hf (J:∀ w,Site (X w).f→Peat G (X w).f) (hw:∀ w x,J w x∈loom G _) (hq:∀ x k,k≤4→2 ≤ k→Ear F x (fun w=>ballX (J w (x w))) v k (d k)) (x:∀ w,Site (X w).c) (a:Axis) k (hk:k≤4)(hy:2 ≤ k): Ear F x (fun w=>ballX (Dart.hum (X w).wood (X w).ρ P.L (Sheaf.leafEdge P.L a) 3 (J w) (x w))) u k (Q k/3):=by
    have he:= tourS (X:=X) (J:=J) hw; obtain ⟨hL,hC⟩:= hLeaf P a; simp_rw[drips (J:=J) x]
    rcases eq_or_lt_of_le hy with hv|hy
    · subst k; exact windQ h x hb he (fun x=>hq x 2 (by decide) le_rfl) _ hL hC
    exact (windB h x hb he k hy hk _ (by decide) _ hL hC).1 (fun x k hi hz=>hq x k (hi.trans hk) hz)
 have hh(j:ℕ): Q j/3 ≤ Q j:=by linarith only [hb.piv j]
 obtain ⟨hM,hg,hQ⟩:= hMain P
 refine ⟨fun a b x k hX hH=> ?_,fun a x k hz he=> (save_y h0 h s hb hp hx a k he hz x).up (hh k),fun a x k hK hC=>?_,fun a x k h' ha=>?_,fun a b i x k hk hi=>?_,fun a b x=>?_,fun a x=>?_,fun a x=>?_⟩
 · obtain ⟨hv,he,hF⟩:= hFlux P a; exact (save_j h0 h s hb hp hx a b k hH hX _ hv he x).up (hh k)
 · dsimp only[Dart.down]; let J:=fun w=>(K w).E a; simp_rw[drips (J:=fun w=>(K w).E a) x]; have ht:= tourS (X:=X) (J:=J) fun w x=>(h0 w).plum a x
   rcases eq_or_lt_of_le hC with he|hy
   · subst k; exact windE h x hb ht (fun x=>s.plum a x _ (by decide) le_rfl) (s.flag a) _ hM hg
   exact (windB h x hb ht k hy hK 5 (by decide) _ hM hg).2 (fun x k hk hh=> s.plum a x k (hk.trans hK) hh)
 · let J:=fun w=>(K w).Q a; have ht:= hf J (fun w x=>(h0 w).plumQ a x) (s.plumQ a) x a k h' ha
   have he:= hTrace P a; exact (ht.plus (save_j h0 h s hb hp hx a a k ha h' _ he.1 he.2 x)).up (by linarith only [hb.piv k])
 · let J:=fun w=>(K w).twist a b i; have ht:= hf J (fun w x=>(h0 w).mint a b i x) (s.mint a b i) x i k hk hi
   have he (i j r:Axis): Ear F x (fun w=> if r=i then ballX ((Dart.hum (X w).wood (X w).ρ P.L (Dart.trace P.L i) 4 ((K w).J i j)) (x w)) else 0) u k (Q k/3):=by
      split_ifs; exact save_j h0 h s hb hp hx i j k hi hk _ (hTrace P i).1 (hTrace P i).2 x; exact Ear.empty (by linarith only [hb.piv k])
   have hh:= ((ht.plus (he a b i)).except (he b a i)).up (show Q k/3+Q k/3+Q k/3≤ Q k from le_of_eq (by ring)); refine hh.likewise (fun w=>?_)
   dsimp only[Dart.down]; split_ifs <;> exact Filter.EventuallyEq.rfl
 · dsimp only[Dart.down]; let J:=fun w=>(K w).J a b; simp_rw [drips (J:=fun w=>(K w).J a b) x]; have ht:= tourS (X:=X) (J:=J) fun w x=>(h0 w).heart a b x
   exact Tour.ink h ht _ _ (hFlux P a).2.2 _ _ (hb.maj 2) (fun i j hi=> north_void i j hi a b) (s.ox a b) (fun i=>s.heart a b i _ (by decide) le_rfl) _
 · let J:=fun w=>(K w).Y a; dsimp only [Dart.down]; simp_rw [dropY (K:=fun w=>(K w).Y a) x]; exact Tour.ink h (tourY (K:=J) fun w x=>(h0 w).palm a x) _ _ hQ _ _ (hb.maj 2) (miss_zero a) (s.orb a) (fun i=>s.palm a i _ (by decide) le_rfl) _
 let J:=fun w=>(K w).E a; dsimp only[Dart.down]; simp_rw [drips (J:=fun w=>(K w).E a) x]; exact Tour.ink h (tourS (J:=J) fun w x=>(h0 w).plum a x) _ _ hQ _ _ (hb.epos 2) (fun i j hi=> rfl) (s.flag a) (fun i=>s.plum a i _ (by decide) le_rfl) _
end YM.Trace.Perfect
#print axioms YM.Trace.Perfect.save_step
