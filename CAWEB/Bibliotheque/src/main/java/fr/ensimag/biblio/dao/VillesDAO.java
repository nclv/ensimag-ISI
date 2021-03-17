package fr.ensimag.biblio.dao;

import java.sql.*;
import javax.sql.DataSource;

public class VillesDAO {
    private DataSource ds;
    
    public VillesDAO(DataSource ds) {
        this.ds = ds;
    }

    public int count(String ville) throws SQLException {
        try (Connection c = ds.getConnection()) {
            PreparedStatement p = c.prepareStatement("SELECT count(*) from Users where ville = ?");
            p.setString(1, ville);
            ResultSet rs = p.executeQuery();
            rs.next();
            return rs.getInt(1);
        }
    }    
}
